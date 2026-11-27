import Std

/-!
# 四列 0/1 填格与长条砖铺法（OEIS A296550）
Lean 4.14.0，单文件，仅依赖标准库。

每行用一个四位数表示，第 j 个二进制位对应从左数第 j 列（从 0 开始）。
上下边界以及越界的左右邻居均视为 0。

运行：lean GridTilings.lean
主定理：corrected。反例：original_fails_at_three。
建模核对：mem_arrays、arrays_nodup、ways_eq_length、mem_tileWords、
tileWords_nodup、board_toTop 与 top_toBoard。
-/
namespace GridTilings

abbrev State := Nat × Nat
def start : State := (0, 0)

private def bit (r j : Nat) : Nat := r / 2^j % 2
private def leftBit (r : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => bit r j

/-- 上、中、下三行分别为 u,v,w。只检查中间一行中的 1。 -/
def legal (u v w : Nat) : Bool :=
  (List.range 4).all fun j =>
    let degree := leftBit v j + bit v (j+1) + bit u j +
      bit u (j+1) + bit w j + leftBit w j
    bit v j == 0 || degree == 3 || degree == 6

private def closes (s : State) : Bool := legal s.1 s.2 0

/-- 枚举可接的非零行。每个行掩码出现一次。 -/
private def next (s : State) : List State :=
  (((List.range 15).map (· + 1)).filter (legal s.1 s.2)).map (s.2, ·)

/-- 在状态 s 后面再填 n 行的合法填法数。读到零行时可以从 start 重启，
    因为零行本身没有需要检查的 1。末尾的边界行不计入高度。 -/
def ways : Nat → State → Nat
  | 0, s => if closes s then 1 else 0
  | n+1, s => (if closes s then ways n start else 0) +
      ((next s).map (ways n)).sum

def arrayCount (n : Nat) : Nat := ways n start

/-! 以下独立核实上面计数器确实数的是原始局部规则允许的数组。 -/
def validFrom (u v : Nat) : List Nat → Bool
  | [] => legal u v 0
  | w :: ws => legal u v w && validFrom v w ws

theorem zero_row (u w : Nat) : legal u 0 w = true := by rfl

private theorem zero_reset (u : Nat) (ws : List Nat) :
    validFrom u 0 ws = validFrom 0 0 ws := by
  cases ws <;> simp [validFrom, zero_row]

/-- 列出所有合法的后续行串，从每个非零行掩码以及零行分别扩展。 -/
def arraysFrom : Nat → State → List (List Nat)
  | 0, s => if closes s then [[]] else []
  | n+1, s =>
      (if closes s then (arraysFrom n start).map (0 :: ·) else []) ++
      (next s).flatMap (fun t => (arraysFrom n t).map (t.2 :: ·))

private theorem length_flatMap' {α β : Type} (xs : List α) (f : α → List β) :
    (xs.flatMap f).length = (xs.map (fun x => (f x).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem ways_eq_length (n : Nat) (s : State) :
    ways n s = (arraysFrom n s).length := by
  induction n generalizing s with
  | zero => simp [ways, arraysFrom]; split <;> rfl
  | succ n ih =>
    simp only [ways, arraysFrom, List.length_append, length_flatMap', List.length_map]
    have hf : ways n = fun t => (arraysFrom n t).length := funext ih
    cases closes s <;> simp [hf]

private theorem mem_next (s t : State) :
    t ∈ next s ↔ t.1 = s.2 ∧ 0 < t.2 ∧ t.2 < 16 ∧ legal s.1 s.2 t.2 = true := by
  rcases s with ⟨u,v⟩
  rcases t with ⟨a,b⟩
  simp [next, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨⟨⟨j, hj, hjb⟩, h⟩, hva⟩
    exact ⟨hva.symm, by omega, by omega, h⟩
  · rintro ⟨rfl, h₁, h₂, h⟩
    exact ⟨⟨⟨b-1, by omega, by omega⟩, h⟩, rfl⟩

private theorem mem_arrays_cons (n : Nat) (s : State) (w : Nat) (ws : List Nat) :
    w :: ws ∈ arraysFrom (n+1) s ↔
      (w = 0 ∧ closes s = true ∧ ws ∈ arraysFrom n start) ∨
      (0 < w ∧ w < 16 ∧ legal s.1 s.2 w = true ∧ ws ∈ arraysFrom n (s.2,w)) := by
  rw [arraysFrom, List.mem_append]
  have hz : w :: ws ∈ (if closes s then (arraysFrom n start).map (0 :: ·) else []) ↔
      w = 0 ∧ closes s = true ∧ ws ∈ arraysFrom n start := by
    cases h : closes s <;> simp [h, List.mem_map, eq_comm]
    exact and_comm
  rw [hz]
  apply or_congr_right
  constructor
  · intro h
    obtain ⟨⟨a,b⟩, ht, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨us, hmem, heq⟩ := List.mem_map.mp hm
    cases heq
    obtain ⟨rfl, hpos, hlt, hlegal⟩ := (mem_next _ _).mp ht
    exact ⟨hpos, hlt, hlegal, hmem⟩
  · rintro ⟨hpos, hlt, hlegal, hmem⟩
    exact List.mem_flatMap.mpr ⟨(s.2,w), (mem_next _ _).mpr ⟨rfl,hpos,hlt,hlegal⟩,
      List.mem_map.mpr ⟨ws,hmem,rfl⟩⟩

/-- 完备性与可靠性：枚举出的行串恰好满足高度、四位行掩码和原题六邻居规则。 -/
theorem mem_arrays (n : Nat) (s : State) (xs : List Nat) :
    xs ∈ arraysFrom n s ↔ xs.length = n ∧ (∀ r ∈ xs, r < 16) ∧ validFrom s.1 s.2 xs = true := by
  induction n generalizing s xs with
  | zero =>
    cases xs <;> cases h : closes s <;> simp [arraysFrom, h, validFrom, closes] at *
  | succ n ih =>
    cases xs with
    | nil =>
      rw [arraysFrom, List.mem_append]
      cases h : closes s <;> simp [h, List.mem_map, List.mem_flatMap]
    | cons w ws =>
      rw [mem_arrays_cons, ih, ih]
      simp only [List.length_cons, Nat.succ.injEq, List.forall_mem_cons, validFrom, Bool.and_eq_true]
      by_cases hw : w = 0
      · subst w
        simp [closes, start, zero_reset, and_comm, and_left_comm, and_assoc]
      · have hp : 0 < w := by omega
        simp [hw, hp, and_comm, and_left_comm, and_assoc]

private theorem prefix_unique {α : Type} (x : α) (xs : List (List α)) (h : xs.Nodup) :
    (xs.map (x :: ·)).Nodup := by
  simpa [List.Nodup, List.pairwise_map] using h

private theorem next_distinct (s : State) :
    (next s).Pairwise (fun a b => a.2 ≠ b.2) := by
  unfold next
  rw [List.pairwise_map]
  apply List.Pairwise.filter
  change (List.map (fun x : Nat => x+1) (List.range 15)).Nodup
  decide

/-- 无重复性：同一个数组在枚举中只出现一次。 -/
theorem arrays_nodup (n : Nat) (s : State) : (arraysFrom n s).Nodup := by
  induction n generalizing s with
  | zero => cases h : closes s <;> simp [arraysFrom, h, List.Nodup]
  | succ n ih =>
    rw [arraysFrom]
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · cases h : closes s
      · exact List.nodup_nil
      · exact prefix_unique _ _ (ih start)
    · apply List.pairwise_flatMap.mpr
      refine ⟨fun s _ => prefix_unique _ _ (ih s), (next_distinct s).imp ?_⟩
      intro a b hab x hx y hy heq
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      exact hab (List.cons.inj heq).1
    · intro x hx y hy heq
      obtain ⟨t,ht,hy'⟩ := List.mem_flatMap.mp hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy'
      cases h : closes s <;> simp [h] at hx
      obtain ⟨_, _, rfl⟩ := hx
      have hpos := ((mem_next _ _).mp ht).2.1
      have := (List.cons.inj heq).1
      omega

private def mass (n : Nat) (ss : List State) := (ss.map (ways n)).sum
private def ends (ss : List State) := (ss.filter closes).length
private def front : Nat → List State
  | 0 => [start]
  | k+1 => (front k).flatMap next

private theorem mass_append (n : Nat) (us vs : List State) :
    mass n (us ++ vs) = mass n us + mass n vs := by
  induction us with
  | nil => simp [mass]
  | cons u us ih =>
    change ways n u + mass n (us ++ vs) = (ways n u + mass n us) + mass n vs
    omega

private theorem expand (n : Nat) (ss : List State) :
    mass (n+1) ss = ends ss * arrayCount n + mass n (ss.flatMap next) := by
  induction ss with
  | nil => simp [mass, ends]
  | cons s ss ih =>
    change ways (n+1) s + mass (n+1) ss = _
    rw [ih, List.flatMap_cons, mass_append]
    cases h : closes s <;>
      simp [ways, h, ends, List.filter_cons, arrayCount, mass, Nat.succ_mul] <;> omega

private theorem layer (n k : Nat) :
    mass (n+1) (front k) = ends (front k) * arrayCount n + mass n (front (k+1)) :=
  expand n (front k)

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

-- 内核检查全部非零前缀；第八层为空，此处的有限检查对所有高度均适用。
private theorem layers :
    ends (front 0) = 1 ∧ ends (front 1) = 0 ∧ ends (front 2) = 0 ∧
    ends (front 3) = 2 ∧ ends (front 4) = 0 ∧ ends (front 5) = 0 ∧
    ends (front 6) = 1 ∧ ends (front 7) = 0 ∧ front 8 = [] := by decide

theorem arrayRec (n : Nat) :
    arrayCount (n+8) = arrayCount (n+7) + 2*arrayCount (n+4) + arrayCount (n+1) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := layers
  have init : arrayCount (n+8) = mass (n+8) (front 0) := by simp [arrayCount,mass,front]
  rw [init, layer (n+7) 0, layer (n+6) 1, layer (n+5) 2, layer (n+4) 3,
      layer (n+3) 4, layer (n+2) 5, layer (n+1) 6, layer n 7]
  simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,mass]
  <;> omega

/-! ## 铺砖的几何模型
每一行是两种记号组成的串。V 表示一块竖砖在本行占一格，
H 表示一块横砖在本行占七格。七行的竖砖所在列必须完全相同。
-/
inductive Strip where
  | V | H
deriving DecidableEq, Repr

open Strip

/-- true 为竖砖所在列，false 为横砖覆盖的列。 -/
def mask : List Strip → List Bool
  | [] => []
  | V :: xs => true :: mask xs
  | H :: xs => List.replicate 7 false ++ mask xs

private theorem mask_inj (xs ys : List Strip) (h : mask xs = mask ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
           | nil => rfl
           | cons t ts => cases t <;> simp [mask, List.replicate] at h
  | cons t xs ih =>
    cases ys with
    | nil => cases t <;> simp [mask, List.replicate] at h
    | cons u ys =>
      cases t <;> cases u <;> simp [mask, List.replicate] at h ⊢ <;> exact ih _ h

/-- 七行分别记录如何铺砖，宽度固定，竖砖须贯穿七行。 -/
structure Board (width : Nat) where
  row : Fin 7 → List Strip
  size : ∀ i, (mask (row i)).length = width
  aligned : ∀ i, mask (row i) = mask (row 0)

theorem board_determined (w : Nat) (b : Board w) (i : Fin 7) :
    b.row i = b.row 0 := mask_inj _ _ (b.aligned i)

/-- 固定宽度的合法单行与完整七行棋盘互相还原。 -/
def toBoard {w : Nat} (p : {xs : List Strip // (mask xs).length = w}) : Board w :=
  ⟨fun _ => p.val, fun _ => p.property, fun _ => rfl⟩

def topRow {w : Nat} (b : Board w) : {xs : List Strip // (mask xs).length = w} :=
  ⟨b.row 0, b.size 0⟩

theorem top_toBoard {w : Nat} (p : {xs : List Strip // (mask xs).length = w}) :
    topRow (toBoard p) = p := rfl

theorem board_toTop {w : Nat} (b : Board w) : toBoard (topRow b) = b := by
  have h : (fun _ : Fin 7 => b.row 0) = b.row := funext fun i => (board_determined w b i).symm
  cases b
  unfold toBoard topRow
  congr

/-- 按最左侧砖的方向枚举所有宽度为 w 的铺砖串。 -/
def tileWords : Nat → List (List Strip)
  | 0 => [[]]
  | w+1 => (tileWords w).map (V :: ·) ++
      match w with
      | k+6 => (tileWords k).map (H :: ·)
      | _ => []

private theorem tileStep (w : Nat) : tileWords (w+1) =
    (tileWords w).map (V :: ·) ++
    (if 6 ≤ w then (tileWords (w-6)).map (H :: ·) else []) := by
  match w with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | k+6 =>
    simp only [Nat.le_add_left, if_true, Nat.add_sub_cancel]
    rfl

/-- 每个铺砖串在且仅在它所覆盖的宽度出现。 -/
theorem mem_tileWords (w : Nat) (xs : List Strip) :
    xs ∈ tileWords w ↔ (mask xs).length = w := by
  induction xs generalizing w with
  | nil =>
    cases w with
    | zero => decide
    | succ w =>
      rw [tileStep]
      split <;> simp [mask, List.mem_map]
  | cons t xs ih =>
    cases w with
    | zero => cases t <;> simp [tileWords, mask]
    | succ w =>
      rw [tileStep]
      split
      next hk =>
        cases t <;> simp [List.mem_map, ih, mask] <;> omega
      next hw =>
        cases t
        · simp [List.mem_map, ih, mask]
        · simp [List.mem_map, mask]
          omega

theorem tileWords_nodup (w : Nat) : (tileWords w).Nodup := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    cases w with
    | zero => decide
    | succ w =>
      rw [tileStep]
      split
      next hk =>
        apply List.pairwise_append.mpr
        refine ⟨prefix_unique V _ (ih _ (by omega)), prefix_unique H _ (ih _ (by omega)), ?_⟩
        intro x hx y hy
        obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨_,_,rfl⟩ := List.mem_map.mp hy
        simp
      next _ =>
        rw [List.append_nil]
        exact prefix_unique _ _ (ih _ (by omega))


def tilingCount (w : Nat) := (tileWords w).length

private theorem tileRec (w : Nat) :
    tilingCount (w+7) = tilingCount (w+6) + tilingCount w := by
  unfold tilingCount
  rw [tileStep]
  simp

private theorem tilePairRec (w : Nat) :
    tilingCount (w+14) = tilingCount (w+12) + 2 * tilingCount (w+6) + tilingCount w := by
  have h₁ : tilingCount (w+14) = tilingCount (w+13) + tilingCount (w+7) := tileRec (w+7)
  have h₂ : tilingCount (w+13) = tilingCount (w+12) + tilingCount (w+6) := tileRec (w+6)
  have h₃ := tileRec w
  omega

private theorem baseValues :
    (List.range 8).map arrayCount = (List.range 8).map (fun n => tilingCount (2*n+2)) := by
  decide

/-- 修正后的猜想：对所有自然数高度 n，合法填法数等于宽 2n+2 的铺法数。 -/
theorem corrected (n : Nat) : arrayCount n = tilingCount (2*n+2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 8
    · have eq := congrArg (fun xs : List Nat => xs[n]?) baseValues
      simpa [List.getElem?_map, List.getElem?_range, h] using eq
    · obtain ⟨m, rfl⟩ : ∃ m, n = m+8 := ⟨n-8, by omega⟩
      rw [arrayRec, ih (m+7) (by omega), ih (m+4) (by omega), ih (m+1) (by omega)]
      have rec := tilePairRec (2*m+4)
      simpa only [Nat.mul_add, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd] using rec.symm

theorem original_fails_at_three : arrayCount 3 = 3 ∧ tilingCount (2*3) = 1 := by decide

/-- 直接比较原始合法行串与七行棋盘唯一编码的无重复枚举长度。 -/
theorem enumeration_sizes (n : Nat) :
    (arraysFrom n start).length = (tileWords (2*n+2)).length := by
  rw [← ways_eq_length]
  exact corrected n

#print axioms GridTilings.corrected
#print axioms GridTilings.enumeration_sizes
#print axioms GridTilings.original_fails_at_three
end GridTilings
