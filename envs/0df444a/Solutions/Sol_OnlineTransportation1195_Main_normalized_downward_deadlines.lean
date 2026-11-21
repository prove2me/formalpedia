-- Prove2me | solution 1 for OnlineTransportation1195.Main.normalized_downward_deadlines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T17:42:05.68047+00:00
-- url     : https://prove2.me/submissions/658c4978-9d2d-4229-a108-a48f7eba58dc

import Theorems.Thm_OnlineTransportation1195_Main_strict_red_weight_budget
import Theorems.Thm_OnlineTransportation1195_Main_root_patch_normalization_iff
import Theorems.Thm_OnlineTransportation1195_Main_detour_budget_inequality

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-!
Blueprint for Theorem 3.1 (`normalized_downward_deadlines`), q419.
Every `sorry` below is a stub proved in a Part file.
-/
/-! ## Walk calculus (Part A) -/
/-- Consecutive vertices are adjacent (no condition on the first vertex). -/
def IsPath (T : Tree n) (L : List (Fin n)) : Prop :=
  ∀ i, i + 1 < L.length → T.Adj (T.vertexAt L i) (T.vertexAt L (i + 1))

/-- Total downward cost of a list. -/
noncomputable def dc (T : Tree n) (L : List (Fin n)) : ℝ :=
  ∑ j ∈ Finset.range (L.length - 1), T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))

/-- `e` is first crossed in `L` at downward cost at most `c`. -/
def VB (T : Tree n) (L : List (Fin n)) (e : Fin n) (c : ℝ) : Prop :=
  ∃ i, T.FirstAt L e i ∧ T.downPrefix L i ≤ c

/-- A closed path at `v`. -/
def ClosedAt (T : Tree n) (v : Fin n) (M : List (Fin n)) : Prop :=
  M.head? = some v ∧ M.getLast? = some v ∧ IsPath T M

theorem VB_mono (T : Tree n) (L : List (Fin n)) (e : Fin n) (c c' : ℝ)
    (h : VB T L e c) (hc : c ≤ c') : VB T L e c' := by
  obtain ⟨i, hi, hc0⟩ := h
  exact ⟨i, hi, hc0.trans hc⟩

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ### Basic helpers -/
/-- Prefix cost of the first `k` steps. -/
noncomputable def pc (T : Tree n) (L : List (Fin n)) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))

theorem downStep_nonneg (T : Tree n) (u v : Fin n) : 0 ≤ T.downStep u v := by
  unfold Tree.downStep
  split_ifs with h
  · exact (T.W_pos v h.1).le
  · exact le_refl 0

theorem downPrefix_eq (T : Tree n) (L : List (Fin n)) (i : ℕ) :
    T.downPrefix L i = pc T L (i + 1) := rfl

theorem dc_eq (T : Tree n) (L : List (Fin n)) : dc T L = pc T L (L.length - 1) := rfl

theorem pc_mono (T : Tree n) (L : List (Fin n)) (a b : ℕ) (h : a ≤ b) :
    pc T L a ≤ pc T L b := by
  unfold pc
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
  intro j _ _
  exact downStep_nonneg T _ _

theorem pc_succ (T : Tree n) (L : List (Fin n)) (k : ℕ) :
    pc T L (k + 1) = pc T L k + T.downStep (T.vertexAt L k) (T.vertexAt L (k + 1)) := by
  unfold pc; rw [Finset.sum_range_succ]

theorem vA_append_left (T : Tree n) (A Z : List (Fin n)) (j : ℕ) (h : j < A.length) :
    T.vertexAt (A ++ Z) j = T.vertexAt A j := by
  unfold Tree.vertexAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem vA_append_right (T : Tree n) (A Z : List (Fin n)) (k : ℕ) :
    T.vertexAt (A ++ Z) (A.length + k) = T.vertexAt Z k := by
  unfold Tree.vertexAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem vA_cons_succ (T : Tree n) (a : Fin n) (Z : List (Fin n)) (k : ℕ) :
    T.vertexAt (a :: Z) (k + 1) = T.vertexAt Z k := by
  unfold Tree.vertexAt; simp

theorem vA_cons_zero (T : Tree n) (a : Fin n) (Z : List (Fin n)) :
    T.vertexAt (a :: Z) 0 = a := by
  unfold Tree.vertexAt; simp

theorem pc_append_left (T : Tree n) (A Z : List (Fin n)) (k : ℕ) (h : k < A.length) :
    pc T (A ++ Z) k = pc T A k := by
  unfold pc
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [vA_append_left T A Z j (by omega), vA_append_left T A Z (j + 1) (by omega)]

theorem shift_vA (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) (k : ℕ) :
    T.vertexAt (L ++ M.tail) (L.length - 1 + k) = T.vertexAt M k := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
    cases M with
    | nil => simp [List.getLast?_eq_some_getLast hL] at hLM
    | cons m M' => exact ⟨m, M', rfl⟩
  cases k with
  | zero =>
    rw [Nat.add_zero, vA_append_left T L _ _ (by omega), vA_cons_zero]
    have h1 : L.getLast? = some m := by rw [← hLM]; rfl
    rw [List.getLast?_eq_some_getLast hL] at h1
    have h2 : L.getLast hL = m := Option.some.inj h1
    unfold Tree.vertexAt
    rw [← h2, List.getLast_eq_getElem]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show L.length - 1 < L.length by omega)]
  | succ k =>
    rw [show L.length - 1 + (k + 1) = L.length + k by omega, vA_append_right, vA_cons_succ]
    rfl

theorem pc_shift (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) (k : ℕ) :
    pc T (L ++ M.tail) (L.length - 1 + k) = dc T L + pc T M k := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  unfold pc
  rw [Finset.sum_range_add]
  congr 1
  · rw [dc_eq]
    exact pc_append_left T L M.tail _ (by omega)
  · apply Finset.sum_congr rfl
    intro j _
    rw [shift_vA T L M hL hLM, Nat.add_assoc, shift_vA T L M hL hLM]

theorem M_ne_nil (L M : List (Fin n)) (hL : L ≠ []) (hLM : M.head? = L.getLast?) : M ≠ [] := by
  rintro rfl
  simp [List.getLast?_eq_some_getLast hL] at hLM

theorem cross_append_left (T : Tree n) (L M : List (Fin n)) (e : Fin n) (j : ℕ)
    (hj : j + 1 < L.length) : T.CrossAt (L ++ M) e j ↔ T.CrossAt L e j := by
  unfold Tree.CrossAt Tree.DownAt Tree.UpAt
  rw [vA_append_left T L M j (by omega), vA_append_left T L M (j + 1) hj]
  simp only [List.length_append]
  constructor
  · rintro (⟨a, _, c, d⟩ | ⟨a, _, c, d⟩)
    · exact Or.inl ⟨a, hj, c, d⟩
    · exact Or.inr ⟨a, hj, c, d⟩
  · rintro (⟨a, _, c, d⟩ | ⟨a, _, c, d⟩)
    · exact Or.inl ⟨a, by omega, c, d⟩
    · exact Or.inr ⟨a, by omega, c, d⟩

theorem cross_lt (T : Tree n) (L : List (Fin n)) (e : Fin n) (j : ℕ)
    (h : T.CrossAt L e j) : j + 1 < L.length := by
  rcases h with h | h
  · exact h.2.1
  · exact h.2.1

theorem cross_shift (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) (e : Fin n) (i : ℕ) (h : T.CrossAt M e i) :
    T.CrossAt (L ++ M.tail) e (L.length - 1 + i) := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  have hlt : (L ++ M.tail).length = L.length - 1 + M.length := by
    have := List.length_pos_iff.mpr (M_ne_nil L M hL hLM)
    simp only [List.length_append, List.length_tail]; omega
  unfold Tree.CrossAt Tree.DownAt Tree.UpAt at *
  rw [hlt, shift_vA T L M hL hLM, Nat.add_assoc, shift_vA T L M hL hLM]
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨a, by omega, c, d⟩
  · exact Or.inr ⟨a, by omega, c, d⟩

/-! ### Part A stubs -/
theorem VB_of_cross (T : Tree n) (L : List (Fin n)) (e : Fin n) (j : ℕ) (c : ℝ)
    (h : T.CrossAt L e j) (hc : T.downPrefix L j ≤ c) : VB T L e c := by
  have hex : ∃ j, T.CrossAt L e j := ⟨j, h⟩
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩, ?_⟩
  refine le_trans ?_ hc
  rw [downPrefix_eq, downPrefix_eq]
  exact pc_mono T L _ _ (by have := Nat.find_min' hex h; omega)

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias VB_of_cross := OnlineTransportation1195.Dev.T31.PartA.VB_of_cross

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem VB_append_left (T : Tree n) (L M : List (Fin n)) (e : Fin n) (c : ℝ)
    (h : VB T L e c) : VB T (L ++ M) e c := by
  obtain ⟨i, ⟨hi, hmin⟩, hc⟩ := h
  have hlt := cross_lt T L e i hi
  refine ⟨i, ⟨(cross_append_left T L M e i hlt).mpr hi, fun j hj hcj => hmin j hj
    ((cross_append_left T L M e j (by omega)).mp hcj)⟩, ?_⟩
  rw [downPrefix_eq, pc_append_left T L M _ hlt]
  exact hc

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias VB_append_left := OnlineTransportation1195.Dev.T31.PartA.VB_append_left

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem VB_append_right (T : Tree n) (L M : List (Fin n)) (e : Fin n) (c : ℝ)
    (hL : L ≠ []) (hM : M.head? = L.getLast?) (h : VB T M e c) :
    VB T (L ++ M.tail) e (dc T L + c) := by
  obtain ⟨i, ⟨hi, _⟩, hc⟩ := h
  apply VB_of_cross T _ e _ _ (cross_shift T L M hL hM e i hi)
  rw [downPrefix_eq, Nat.add_assoc, pc_shift T L M hL hM, ← downPrefix_eq]
  linarith

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias VB_append_right := OnlineTransportation1195.Dev.T31.PartA.VB_append_right

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem isPath_append (T : Tree n) (L M : List (Fin n)) (hL : IsPath T L) (hM : IsPath T M)
    (hLM : M.head? = L.getLast?) : IsPath T (L ++ M.tail) := by
  intro j hj
  rcases eq_or_ne L [] with rfl | hL0
  · simp at hLM
    subst hLM; simp at hj
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL0
  have hMl := List.length_pos_iff.mpr (M_ne_nil L M hL0 hLM)
  have hlt : (L ++ M.tail).length = L.length - 1 + M.length := by
    simp only [List.length_append, List.length_tail]; omega
  by_cases hjL : j + 1 < L.length
  · rw [vA_append_left T L _ _ (by omega), vA_append_left T L _ _ hjL]
    exact hL j hjL
  · obtain ⟨k, rfl⟩ : ∃ k, j = L.length - 1 + k := ⟨j - (L.length - 1), by omega⟩
    rw [shift_vA T L M hL0 hLM, Nat.add_assoc, shift_vA T L M hL0 hLM]
    exact hM k (by omega)

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias isPath_append := OnlineTransportation1195.Dev.T31.PartA.isPath_append

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dc_append (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) : dc T (L ++ M.tail) = dc T L + dc T M := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  have hMl := List.length_pos_iff.mpr (M_ne_nil L M hL hLM)
  rw [dc_eq, dc_eq T M, ← pc_shift T L M hL hLM]
  congr 1
  simp only [List.length_append, List.length_tail]; omega

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias dc_append := OnlineTransportation1195.Dev.T31.PartA.dc_append

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem getLast_append_tail (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) : (L ++ M.tail).getLast? = M.getLast? := by
  obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
    cases M with
    | nil => simp [List.getLast?_eq_some_getLast hL] at hLM
    | cons m M' => exact ⟨m, M', rfl⟩
  rcases eq_or_ne M' [] with rfl | hM'
  · simp only [List.tail_cons, List.append_nil]
    rw [← hLM]; rfl
  · simp only [List.tail_cons]
    rw [List.getLast?_append_of_ne_nil _ hM', List.getLast?_cons, List.getLast?_eq_some_getLast hM']
    rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias getLast_append_tail := OnlineTransportation1195.Dev.T31.PartA.getLast_append_tail

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem head_append (L M : List (Fin n)) (hL : L ≠ []) : (L ++ M).head? = L.head? := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a L => rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias head_append := OnlineTransportation1195.Dev.T31.PartA.head_append

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ### Upward path -/
theorem downStep_parent (T : Tree n) (u : Fin n) : T.downStep u (T.parent u) = 0 := by
  unfold Tree.downStep
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have hu : u ≠ T.root := by
    rintro rfl; exact h1 T.parent_root
  have d1 := T.depth_parent u hu
  have d2 := T.depth_parent (T.parent u) h1
  rw [h2] at d2
  omega

theorem iter_depth (T : Tree n) : ∀ (k : ℕ) (v : Fin n), T.depth v = k →
    T.parent^[k] v = T.root := by
  intro k
  induction k with
  | zero =>
    intro v hv
    by_contra hne
    have := T.depth_parent v hne
    simp at hne
    omega
  | succ k ih =>
    intro v hv
    have hne : v ≠ T.root := by
      rintro rfl; rw [T.depth_root] at hv; omega
    have := T.depth_parent v hne
    rw [Function.iterate_succ_apply]
    exact ih _ (by omega)

theorem depth_iter (T : Tree n) (v : Fin n) : ∀ i, i ≤ T.depth v →
    T.depth (T.parent^[i] v) + i = T.depth v := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hne : T.parent^[i] v ≠ T.root := by
      intro h; rw [h, T.depth_root] at h1; omega
    have := T.depth_parent _ hne
    rw [Function.iterate_succ_apply']
    omega

theorem iter_ne_root (T : Tree n) (v : Fin n) (i : ℕ) (hi : i < T.depth v) :
    T.parent^[i] v ≠ T.root := by
  intro h
  have := depth_iter T v i hi.le
  rw [h, T.depth_root] at this
  omega

theorem vA_up (T : Tree n) (v : Fin n) (i : ℕ) (hi : i < T.depth v + 1) :
    T.vertexAt ((List.range (T.depth v + 1)).map (fun i => T.parent^[i] v)) i =
      T.parent^[i] v := by
  unfold Tree.vertexAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem up_path (T : Tree n) (v : Fin n) :
    ∃ U : List (Fin n), U.head? = some v ∧ U.getLast? = some T.root ∧ IsPath T U ∧
      dc T U = 0 := by
  refine ⟨(List.range (T.depth v + 1)).map (fun i => T.parent^[i] v), ?_, ?_, ?_, ?_⟩
  · simp [List.range_succ_eq_map]
  · rw [List.range_succ]
    simp [iter_depth T _ v rfl]
  · intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [vA_up T v i (by omega), vA_up T v (i + 1) hi, Function.iterate_succ_apply']
    exact Or.inr ⟨iter_ne_root T v i (by omega), rfl⟩
  · unfold dc
    apply Finset.sum_eq_zero
    intro i hi
    simp only [List.length_map, List.length_range, Finset.mem_range] at hi
    rw [vA_up T v i (by omega), vA_up T v (i + 1) (by omega), Function.iterate_succ_apply']
    exact downStep_parent T _

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias up_path := OnlineTransportation1195.Dev.T31.PartA.up_path

/-! ## Blocks: inserting closed detours into a path (Part A) -/
/-- Replace the `i`-th vertex of `L` by the closed path `D i` at it. -/
noncomputable def blocks (L : List (Fin n)) (D : ℕ → List (Fin n)) : List (Fin n) :=
  ((List.range L.length).map D).flatten

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ### Junctions -/
theorem vA_head (T : Tree n) (X : List (Fin n)) (x : Fin n) (h : X.head? = some x) :
    T.vertexAt X 0 = x := by
  cases X with
  | nil => simp at h
  | cons y X => simp at h; subst h; exact vA_cons_zero T _ _

theorem cons_eq_pair (a c : Fin n) (C : List (Fin n)) (hC : C.head? = some c) :
    a :: C = [a, c] ++ C.tail := by
  cases C with
  | nil => simp at hC
  | cons y C => simp at hC; subst hC; rfl

theorem dc_pair (T : Tree n) (a c : Fin n) : dc T [a, c] = T.downStep a c := by
  simp [dc, Tree.vertexAt]

theorem dc_cons (T : Tree n) (a c : Fin n) (C : List (Fin n)) (hC : C.head? = some c) :
    dc T (a :: C) = T.downStep a c + dc T C := by
  rw [cons_eq_pair a c C hC, dc_append T [a, c] C (by simp) (by rw [hC]; rfl), dc_pair]

theorem dc_junction (T : Tree n) (A C : List (Fin n)) (a c : Fin n) (hA : A ≠ [])
    (ha : A.getLast? = some a) (hc : C.head? = some c) :
    dc T (A ++ C) = dc T A + T.downStep a c + dc T C := by
  have h1 := dc_append T A (a :: C) hA (by rw [ha]; rfl)
  rw [List.tail_cons] at h1
  rw [h1, dc_cons T a c C hc, add_assoc]

theorem isPath_junction (T : Tree n) (A C : List (Fin n)) (a c : Fin n)
    (ha : A.getLast? = some a) (hc : C.head? = some c)
    (hpA : IsPath T A) (hadj : T.Adj a c) (hpC : IsPath T C) : IsPath T (A ++ C) := by
  have hp2 : IsPath T [a, c] := by
    intro i hi
    simp at hi
    subst hi
    simpa [Tree.vertexAt] using hadj
  have h1 : IsPath T (a :: C) := by
    rw [cons_eq_pair a c C hc]
    exact isPath_append T [a, c] C hp2 hpC (by rw [hc]; rfl)
  have h2 := isPath_append T A (a :: C) hpA h1 (by rw [ha]; rfl)
  rwa [List.tail_cons] at h2

theorem VB_junction (T : Tree n) (A C : List (Fin n)) (a c : Fin n) (hA : A ≠ [])
    (ha : A.getLast? = some a) (hc : C.head? = some c) (e : Fin n) (x : ℝ)
    (h : VB T C e x) : VB T (A ++ C) e (dc T A + (T.downStep a c + x)) := by
  have h1 : VB T (a :: C) e (T.downStep a c + x) := by
    have := VB_append_right T [a, c] C e x (by simp) (by rw [hc]; rfl) h
    rwa [← cons_eq_pair a c C hc, dc_pair] at this
  have h2 := VB_append_right T A (a :: C) e _ hA (by rw [ha]; rfl) h1
  rwa [List.tail_cons] at h2

/-! ### Blocks -/
noncomputable def B (D : ℕ → List (Fin n)) (k : ℕ) : List (Fin n) :=
  ((List.range k).map D).flatten

theorem B_succ (D : ℕ → List (Fin n)) (k : ℕ) : B D (k + 1) = B D k ++ D k := by
  simp [B, List.range_succ]

theorem B_one (D : ℕ → List (Fin n)) : B D 1 = D 0 := by
  simp [B]

theorem B_prefix (D : ℕ → List (Fin n)) (k m : ℕ) (h : k ≤ m) :
    ∃ Z, B D m = B D k ++ Z := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m _ ih =>
    obtain ⟨Z, hZ⟩ := ih
    exact ⟨Z ++ D m, by rw [B_succ, hZ, List.append_assoc]⟩

theorem blocks_eq (L : List (Fin n)) (D : ℕ → List (Fin n)) : blocks L D = B D L.length := rfl

theorem closed_ne_nil (T : Tree n) (v : Fin n) (M : List (Fin n)) (h : ClosedAt T v M) :
    M ≠ [] := by
  rintro rfl; simp [ClosedAt] at h

theorem B_inv (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    ∀ k, k + 1 ≤ L.length →
      B D (k + 1) ≠ [] ∧ (B D (k + 1)).head? = some (T.vertexAt L 0) ∧
      (B D (k + 1)).getLast? = some (T.vertexAt L k) ∧
      dc T (B D (k + 1)) = pc T L k + ∑ j ∈ Finset.range (k + 1), dc T (D j) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 := hD 0 (by omega)
    rw [B_one]
    refine ⟨closed_ne_nil T _ _ h0, h0.1, h0.2.1, ?_⟩
    simp [pc]
  | succ k ih =>
    intro hk
    obtain ⟨hne, hh, hl, hdc⟩ := ih (by omega)
    have hk1 := hD (k + 1) (by omega)
    have hCne := closed_ne_nil T _ _ hk1
    rw [B_succ]
    refine ⟨by simp [hne], by rw [head_append _ _ hne, hh], ?_, ?_⟩
    · rw [List.getLast?_append_of_ne_nil _ hCne, hk1.2.1]
    · rw [dc_junction T _ _ _ _ hne hl hk1.1, hdc, pc_succ, Finset.sum_range_succ _ (k + 1)]
      ring

theorem B_isPath (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n)) (hL : IsPath T L)
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    ∀ k, k + 1 ≤ L.length → IsPath T (B D (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [B_one]; exact (hD 0 (by omega)).2.2
  | succ k ih =>
    intro hk
    obtain ⟨_, _, hl, _⟩ := B_inv T L D hD k (by omega)
    have hk1 := hD (k + 1) (by omega)
    rw [B_succ]
    exact isPath_junction T _ _ _ _ hl hk1.1 (ih (by omega)) (hL k (by omega)) hk1.2.2

theorem blocks_head (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    (blocks L D).head? = L.head? := by
  cases L with
  | nil => simp [blocks]
  | cons a L =>
    have := (B_inv T (a :: L) D hD L.length (by simp)).2.1
    rw [blocks_eq]
    simp only [List.length_cons] at this ⊢
    rw [this, vA_cons_zero]; rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias blocks_head := OnlineTransportation1195.Dev.T31.PartA.blocks_head

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem blocks_isPath (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hL : IsPath T L) (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    IsPath T (blocks L D) := by
  cases L with
  | nil => intro i hi; simp [blocks] at hi
  | cons a L =>
    have := B_isPath T (a :: L) D hL hD L.length (by simp)
    rw [blocks_eq]
    simpa using this

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias blocks_isPath := OnlineTransportation1195.Dev.T31.PartA.blocks_isPath

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem blocks_step (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) (i : ℕ) (hi : i + 1 < L.length) :
    ∃ p, p + 1 < (blocks L D).length ∧
      T.vertexAt (blocks L D) p = T.vertexAt L i ∧
      T.vertexAt (blocks L D) (p + 1) = T.vertexAt L (i + 1) ∧
      T.downPrefix (blocks L D) p =
        T.downPrefix L i + ∑ j ∈ Finset.range (i + 1), dc T (D j) := by
  obtain ⟨hne, _, hl, hdc⟩ := B_inv T L D hD i (by omega)
  have hC := hD (i + 1) hi
  have hCne := closed_ne_nil T _ _ hC
  obtain ⟨Z, hZ⟩ := B_prefix D (i + 2) L.length (by omega)
  rw [B_succ] at hZ
  set A := B D (i + 1) with hAdef
  set a := T.vertexAt L i with hadef
  set Y := D (i + 1) ++ Z with hYdef
  have hbl : blocks L D = A ++ (a :: Y).tail := by
    rw [blocks_eq, hZ, List.tail_cons, List.append_assoc]
  have hlink : (a :: Y).head? = A.getLast? := by rw [hl]; rfl
  have hAl : 0 < A.length := List.length_pos_iff.mpr hne
  have hCl : 0 < (D (i + 1)).length := List.length_pos_iff.mpr hCne
  have hY0 : T.vertexAt Y 0 = T.vertexAt L (i + 1) := by
    rw [hYdef, vA_append_left T _ _ 0 hCl]
    exact vA_head T _ _ hC.1
  refine ⟨A.length - 1, ?_, ?_, ?_, ?_⟩
  · rw [hbl]; simp [hYdef]; omega
  · rw [hbl, ← Nat.add_zero (A.length - 1), shift_vA T A _ hne hlink, vA_cons_zero]
  · rw [hbl, shift_vA T A _ hne hlink, vA_cons_succ, hY0]
  · rw [downPrefix_eq, hbl, pc_shift T A _ hne hlink, hdc, downPrefix_eq, pc_succ T L i,
      pc_succ, vA_cons_zero, vA_cons_succ, hY0]
    simp [pc]
    ring

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias blocks_step := OnlineTransportation1195.Dev.T31.PartA.blocks_step

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dc_take (T : Tree n) (L : List (Fin n)) (k : ℕ) (hk : k < L.length) :
    dc T (L.take (k + 1)) = pc T L k := by
  have hlen : (L.take (k + 1)).length = k + 1 := by simp; omega
  rw [dc_eq, hlen, Nat.add_sub_cancel]
  have := pc_append_left T (L.take (k + 1)) (L.drop (k + 1)) k (by omega)
  rw [List.take_append_drop] at this
  exact this.symm

theorem blocks_VB (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) (i : ℕ) (hi : i < L.length)
    (e : Fin n) (c : ℝ) (h : VB T (D i) e c) :
    VB T (blocks L D) e (dc T (L.take (i + 1)) + ∑ j ∈ Finset.range i, dc T (D j) + c) := by
  obtain ⟨Z, hZ⟩ := B_prefix D (i + 1) L.length (by omega)
  rw [blocks_eq, hZ, dc_take T L i hi]
  cases i with
  | zero =>
    rw [B_one]
    have := VB_append_left T (D 0) Z e c h
    refine VB_mono T _ e _ _ this (le_of_eq ?_)
    simp [pc]
  | succ i =>
    obtain ⟨hne, _, hl, hdc⟩ := B_inv T L D hD i (by omega)
    have hC := hD (i + 1) hi
    rw [B_succ]
    have := VB_append_left T _ Z e _ (VB_junction T _ _ _ _ hne hl hC.1 e c h)
    refine VB_mono T _ e _ _ this (le_of_eq ?_)
    rw [hdc, pc_succ]
    ring

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias blocks_VB := OnlineTransportation1195.Dev.T31.PartA.blocks_VB

/-! ## Restricted depth-first search (Part B) -/
noncomputable def children (T : Tree n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun c => decide (c ≠ T.root ∧ T.parent c = v))

/-- Depth-first search from `v` using only the child edges in `S`, with fuel. -/
noncomputable def dfsF (T : Tree n) (S : Finset (Fin n)) : ℕ → Fin n → List (Fin n)
  | 0, v => [v]
  | k + 1, v => v :: ((children T v).filter (fun c => decide (c ∈ S))).flatMap
      (fun c => dfsF T S k c ++ [v])

noncomputable def dfsS (T : Tree n) (S : Finset (Fin n)) (v : Fin n) : List (Fin n) :=
  dfsF T S n v

/-- The edge `e` hangs below `v` and every edge from `v` down to `e` lies in `S`. -/
def Reach (T : Tree n) (S : Finset (Fin n)) (v e : Fin n) : Prop :=
  e ∈ S ∧ e ≠ v ∧ T.IsAnc v e ∧
    ∀ f, f ≠ T.root → f ≠ v → T.IsAnc v f → T.IsAnc f e → f ∈ S

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## Step sums -/
/-- Sum of a function over the consecutive steps of a list. -/
noncomputable def SS {M : Type} [AddCommMonoid M] (T : Tree n) (φ : Fin n → Fin n → M)
    (L : List (Fin n)) : M :=
  ∑ j ∈ Finset.range (L.length - 1), φ (T.vertexAt L j) (T.vertexAt L (j + 1))

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable {M : Type} [AddCommMonoid M] (T : Tree n) (φ : Fin n → Fin n → M)
theorem SS_single (a : Fin n) : SS T φ [a] = 0 := by simp [SS]

theorem SS_cons2 (a b : Fin n) (L : List (Fin n)) :
    SS T φ (a :: b :: L) = φ a b + SS T φ (b :: L) := by
  simp only [SS, List.length_cons]
  rw [show L.length + 1 + 1 - 1 = L.length + 1 by omega, Finset.sum_range_succ',
    show L.length + 1 - 1 = L.length by omega]
  rw [add_comm]; rfl

theorem SS_append (L : List (Fin n)) (u b : Fin n) (R : List (Fin n))
    (hL : L.getLast? = some u) :
    SS T φ (L ++ b :: R) = SS T φ L + φ u b + SS T φ (b :: R) := by
  induction L with
  | nil => simp at hL
  | cons a L ih =>
    cases L with
    | nil =>
      simp at hL; subst hL
      simp [SS_cons2, SS_single]
    | cons a' L =>
      rw [List.getLast?_cons_cons] at hL
      rw [List.cons_append, List.cons_append, SS_cons2, ← List.cons_append, ih hL, SS_cons2]
      simp only [add_assoc]

theorem SS_flatMap (v : Fin n) (cs : List (Fin n)) (A : Fin n → List (Fin n))
    (hA : ∀ c ∈ cs, (A c).head? = some c ∧ (A c).getLast? = some c) :
    SS T φ (v :: cs.flatMap (fun c => A c ++ [v])) =
      (cs.map (fun c => φ v c + SS T φ (A c) + φ c v)).sum := by
  induction cs with
  | nil => simp [SS_single]
  | cons c cs ih =>
    have h1 := hA c (by simp)
    have ih' := ih (fun c' hc' => hA c' (by simp [hc']))
    obtain ⟨A', hA'⟩ : ∃ A', A c = c :: A' := by
      cases h : A c with
      | nil => rw [h] at h1; simp at h1
      | cons x A' => rw [h] at h1; simp at h1; exact ⟨A', by rw [h1.1]⟩
    have e1 : v :: (c :: cs).flatMap (fun c => A c ++ [v]) =
        (v :: A c) ++ v :: cs.flatMap (fun c => A c ++ [v]) := by simp
    have hl : (v :: A c).getLast? = some c := by
      rw [hA', List.getLast?_cons_cons, ← hA']; exact h1.2
    rw [e1, SS_append T φ _ c v _ hl, ih', List.map_cons, List.sum_cons, hA', SS_cons2]

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem getLast_flatMap (v : Fin n) (cs : List (Fin n)) (A : Fin n → List (Fin n)) :
    (v :: cs.flatMap (fun c => A c ++ [v])).getLast? = some v := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have e1 : v :: (c :: cs).flatMap (fun c => A c ++ [v]) =
        (v :: A c) ++ v :: cs.flatMap (fun c => A c ++ [v]) := by simp
    rw [e1, List.getLast?_append, ih]
    rfl

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n))
/-! ## DFS structure -/
theorem dfsF_succ (k : ℕ) (v : Fin n) :
    dfsF T S (k + 1) v = v :: ((children T v).filter (fun c => decide (c ∈ S))).flatMap
      (fun c => dfsF T S k c ++ [v]) := rfl

theorem dfsF_head (k : ℕ) (v : Fin n) : (dfsF T S k v).head? = some v := by
  cases k <;> rfl

theorem dfsF_last (k : ℕ) (v : Fin n) : (dfsF T S k v).getLast? = some v := by
  cases k with
  | zero => rfl
  | succ k => rw [dfsF_succ]; exact getLast_flatMap v _ _

theorem mem_cs (v c : Fin n) :
    c ∈ (children T v).filter (fun c => decide (c ∈ S)) ↔
      (c ≠ T.root ∧ T.parent c = v) ∧ c ∈ S := by
  simp [children]; tauto

theorem nodup_cs (v : Fin n) : ((children T v).filter (fun c => decide (c ∈ S))).Nodup :=
  ((List.nodup_finRange n).filter _).filter _

theorem SS_dfsF_succ {M : Type} [AddCommMonoid M] (φ : Fin n → Fin n → M) (k : ℕ) (v : Fin n) :
    SS T φ (dfsF T S (k + 1) v) =
      ∑ c ∈ ((children T v).filter (fun c => decide (c ∈ S))).toFinset,
        (φ v c + SS T φ (dfsF T S k c) + φ c v) := by
  rw [dfsF_succ, SS_flatMap T φ v _ _ (fun c _ => ⟨dfsF_head T S k c, dfsF_last T S k c⟩),
    List.sum_toFinset _ (nodup_cs T S v)]

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n)
/-! ## Tree facts -/
theorem depth_eq_zero {e : Fin n} (h : T.depth e = 0) : e = T.root := by
  by_contra hne
  have := T.depth_parent e hne
  omega

theorem depth_child {c : Fin n} (hc : c ≠ T.root) : T.depth c = T.depth (T.parent c) + 1 :=
  (T.depth_parent c hc).symm

theorem depth_iter (e : Fin n) : ∀ i, T.depth (T.parent^[i] e) = T.depth e - i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    by_cases hx : T.parent^[i] e = T.root
    · rw [hx, T.parent_root, T.depth_root]
      rw [hx, T.depth_root] at ih
      omega
    · have := T.depth_parent _ hx
      omega

theorem iter_root (i : ℕ) : T.parent^[i] T.root = T.root :=
  Function.iterate_fixed T.parent_root i

theorem iter_depth (e : Fin n) : T.parent^[T.depth e] e = T.root :=
  depth_eq_zero T (by rw [depth_iter]; simp)

theorem anc_eq {a e : Fin n} (h : T.IsAnc a e) :
    a = T.parent^[T.depth e - T.depth a] e ∧ T.depth a ≤ T.depth e := by
  obtain ⟨i, rfl⟩ := h
  rw [depth_iter]
  by_cases hi : i ≤ T.depth e
  · refine ⟨?_, by omega⟩
    congr 1; omega
  · have h1 : T.parent^[i] e = T.root := by
      rw [show i = (i - T.depth e) + T.depth e by omega, Function.iterate_add_apply,
        iter_depth, iter_root]
    refine ⟨?_, by omega⟩
    rw [h1, show T.depth e - (T.depth e - i) = T.depth e by omega, iter_depth]

theorem anc_refl (a : Fin n) : T.IsAnc a a := ⟨0, rfl⟩

theorem anc_parent {c : Fin n} : T.IsAnc (T.parent c) c := ⟨1, rfl⟩

theorem anc_trans' {a b c : Fin n} (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) : T.IsAnc a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply]⟩

theorem anc_of_depth {a b e : Fin n} (ha : T.IsAnc a e) (hb : T.IsAnc b e)
    (hd : T.depth a ≤ T.depth b) : T.IsAnc a b := by
  obtain ⟨ha1, ha2⟩ := anc_eq T ha
  obtain ⟨hb1, hb2⟩ := anc_eq T hb
  refine ⟨T.depth b - T.depth a, ?_⟩
  have h3 : T.parent^[T.depth b - T.depth a] (T.parent^[T.depth e - T.depth b] e) =
      T.parent^[T.depth e - T.depth a] e := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  rw [← hb1] at h3
  exact h3.trans ha1.symm

theorem anc_eq_of_depth {a b e : Fin n} (ha : T.IsAnc a e) (hb : T.IsAnc b e)
    (hd : T.depth a = T.depth b) : a = b := by
  rw [(anc_eq T ha).1, (anc_eq T hb).1, hd]

theorem anc_lt {a e : Fin n} (h : T.IsAnc a e) (hne : a ≠ e) : T.depth a < T.depth e := by
  rcases lt_or_eq_of_le (anc_eq T h).2 with h1 | h1
  · exact h1
  · exact absurd (anc_eq_of_depth T h (anc_refl T e) h1) hne

theorem no2cycle {c : Fin n} (hc : c ≠ T.root) : T.parent (T.parent c) ≠ c := by
  intro h
  by_cases hp : T.parent c = T.root
  · rw [hp, T.parent_root] at h; exact hc h.symm
  · have h1 := T.depth_parent _ hp
    have h2 := T.depth_parent _ hc
    rw [h] at h1
    omega

theorem depth_lt (e : Fin n) : T.depth e < n := by
  have hinj : Function.Injective (fun i : Fin (T.depth e + 1) => T.parent^[i] e) := by
    intro i j hij
    have := congrArg T.depth hij
    simp only [depth_iter] at this
    ext; omega
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n))
/-! ## Reachability decomposition -/
theorem reach_depth {v e : Fin n} (h : Reach T S v e) : T.depth v < T.depth e :=
  anc_lt T h.2.2.1 (fun h' => h.2.1 h'.symm)

theorem reach_iff (v e : Fin n) :
    Reach T S v e ↔ ∃ c, ((c ≠ T.root ∧ T.parent c = v) ∧ c ∈ S) ∧ (c = e ∨ Reach T S c e) := by
  constructor
  · rintro ⟨heS, hev, hve, hpath⟩
    have hd := anc_lt T hve (fun h => hev h.symm)
    set c := T.parent^[T.depth e - T.depth v - 1] e with hcdef
    have hce : T.IsAnc c e := ⟨_, rfl⟩
    have hdc : T.depth c = T.depth v + 1 := by rw [hcdef, depth_iter]; omega
    have hcr : c ≠ T.root := by
      intro h; rw [h, T.depth_root] at hdc; omega
    have hvc : T.IsAnc v c := anc_of_depth T hve hce (by omega)
    have hpc : T.parent c = v := by
      refine anc_eq_of_depth T (anc_trans' T (anc_parent T) hce) hve ?_
      have := depth_child T hcr; omega
    have hcv : c ≠ v := by intro h; rw [h] at hdc; omega
    refine ⟨c, ⟨⟨hcr, hpc⟩, hpath c hcr hcv hvc hce⟩, ?_⟩
    by_cases hc : c = e
    · exact Or.inl hc
    · refine Or.inr ⟨heS, fun h => hc h.symm, hce, ?_⟩
      intro f hfr hfc hcf hfe
      refine hpath f hfr ?_ (anc_trans' T hvc hcf) hfe
      intro h; rw [h] at hcf; have := anc_lt T hcf (fun h' => hcv h'); omega
  · rintro ⟨c, ⟨⟨hcr, hpc⟩, hcS⟩, hce⟩
    have hce' : T.IsAnc c e := by
      rcases hce with h | h
      · rw [h]; exact anc_refl T e
      · exact h.2.2.1
    have heS : e ∈ S := by
      rcases hce with h | h
      · rw [← h]; exact hcS
      · exact h.1
    have hdc := depth_child T hcr
    rw [hpc] at hdc
    have hdce := (anc_eq T hce').2
    have hvc : T.IsAnc v c := by rw [← hpc]; exact anc_parent T
    refine ⟨heS, ?_, anc_trans' T hvc hce', ?_⟩
    · intro h; rw [h] at hdce; omega
    · intro f hfr hfv hvf hfe
      have hdf := anc_lt T hvf (fun h => hfv h.symm)
      by_cases hle : T.depth f ≤ T.depth c
      · have : f = c := anc_eq_of_depth T hfe hce' (by omega)
        rw [this]; exact hcS
      · have hcf := anc_of_depth T hce' hfe (by omega)
        rcases hce with h | h
        · have := (anc_eq T hfe).2; rw [← h] at this; omega
        · exact h.2.2.2 f hfr (fun h' => by rw [h'] at hle; omega) hcf hfe

theorem child_unique {v c c' e : Fin n} (hc : c ≠ T.root ∧ T.parent c = v)
    (hc' : c' ≠ T.root ∧ T.parent c' = v) (he : T.IsAnc c e) (he' : T.IsAnc c' e) : c = c' := by
  refine anc_eq_of_depth T he he' ?_
  rw [depth_child T hc.1, depth_child T hc'.1, hc.2, hc'.2]

theorem cond_anc {c e : Fin n} (h : c = e ∨ Reach T S c e) : T.IsAnc c e := by
  rcases h with h | h
  · rw [h]; exact anc_refl T e
  · exact h.2.2.1

/-- The per-edge count of a step pattern along a DFS. -/
theorem count_dfsF (e : Fin n) (φ : Fin n → Fin n → ℕ)
    (hφ : ∀ c, c ≠ T.root → φ (T.parent c) c + φ c (T.parent c) = if c = e then 1 else 0) :
    ∀ k v, T.depth e < T.depth v + k →
      SS T φ (dfsF T S k v) = if Reach T S v e then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro v hk
    have : ¬ Reach T S v e := fun h => by have := reach_depth T S h; omega
    rw [if_neg this]
    exact SS_single T φ v
  | succ k ih =>
    intro v hk
    rw [SS_dfsF_succ]
    have hterm : ∀ c ∈ ((children T v).filter (fun c => decide (c ∈ S))).toFinset,
        φ v c + SS T φ (dfsF T S k c) + φ c v = if (c = e ∨ Reach T S c e) then 1 else 0 := by
      intro c hc
      rw [List.mem_toFinset, mem_cs] at hc
      obtain ⟨⟨hcr, hpc⟩, _⟩ := hc
      have hd := depth_child T hcr
      rw [ih c (by rw [hpc] at hd; omega)]
      have h1 := hφ c hcr
      rw [hpc] at h1
      by_cases hce : c = e
      · have : ¬ Reach T S c e := fun h => h.2.1 hce.symm
        simp only [if_neg this, if_pos (Or.inl hce : c = e ∨ Reach T S c e)]
        rw [if_pos hce] at h1; omega
      · rw [if_neg hce] at h1
        by_cases hr : Reach T S c e
        · simp only [if_pos hr, if_pos (Or.inr hr : c = e ∨ Reach T S c e)]; omega
        · have : ¬ (c = e ∨ Reach T S c e) := by tauto
          simp only [if_neg hr, if_neg this]; omega
    rw [Finset.sum_congr rfl hterm]
    by_cases hR : Reach T S v e
    · rw [if_pos hR]
      obtain ⟨c, hc, hce⟩ := (reach_iff T S v e).mp hR
      rw [Finset.sum_eq_single c]
      · rw [if_pos hce]
      · intro b hb hbc
        rw [List.mem_toFinset, mem_cs] at hb
        rw [if_neg]
        intro hbe
        exact hbc (child_unique T hb.1 hc.1 (cond_anc T S hbe) (cond_anc T S hce))
      · intro hc'
        exact absurd (by rw [List.mem_toFinset, mem_cs]; exact hc) hc'
    · rw [if_neg hR]
      refine Finset.sum_eq_zero ?_
      intro c hc
      rw [List.mem_toFinset, mem_cs] at hc
      rw [if_neg]
      intro hce
      exact hR ((reach_iff T S v e).mpr ⟨c, hc, hce⟩)

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n)
/-! ## Applications -/
/-- Indicator of a non-adjacent step. -/
noncomputable def bad (T : Tree n) (u w : Fin n) : ℕ := if T.Adj u w then 0 else 1

/-- Indicator of a downward step across `e`. -/
noncomputable def dφ (T : Tree n) (e u w : Fin n) : ℕ := if u = T.parent e ∧ w = e then 1 else 0

/-- Indicator of an upward step across `e`. -/
noncomputable def uφ (T : Tree n) (e u w : Fin n) : ℕ := if u = e ∧ w = T.parent e then 1 else 0

theorem isPath_iff (L : List (Fin n)) : IsPath T L ↔ SS T (bad T) L = 0 := by
  unfold SS IsPath
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj
    rw [Finset.mem_range] at hj
    simp [bad, h j (by omega)]
  · intro h i hi
    have := h i (Finset.mem_range.mpr (by omega))
    simp only [bad] at this
    by_contra hc
    rw [if_neg hc] at this
    exact one_ne_zero this

theorem SS_bad_dfsF (S : Finset (Fin n)) : ∀ k v, SS T (bad T) (dfsF T S k v) = 0 := by
  intro k
  induction k with
  | zero => intro v; exact SS_single T _ v
  | succ k ih =>
    intro v
    rw [SS_dfsF_succ]
    refine Finset.sum_eq_zero ?_
    intro c hc
    rw [List.mem_toFinset, mem_cs] at hc
    obtain ⟨⟨hcr, hpc⟩, _⟩ := hc
    have h1 : T.Adj v c := Or.inl ⟨hcr, hpc⟩
    have h2 : T.Adj c v := Or.inr ⟨hcr, hpc⟩
    simp [bad, h1, h2, ih c]

theorem dφ_spec (e : Fin n) (he : e ≠ T.root) :
    ∀ c, c ≠ T.root → dφ T e (T.parent c) c + dφ T e c (T.parent c) = if c = e then 1 else 0 := by
  intro c hc
  have h2 : ¬ (c = T.parent e ∧ T.parent c = e) := by
    rintro ⟨h1, h2⟩
    exact no2cycle T he (by rw [← h1, h2])
  unfold dφ
  rw [if_neg h2]
  by_cases hce : c = e
  · subst hce; simp
  · simp [hce]

theorem uφ_spec (e : Fin n) (he : e ≠ T.root) :
    ∀ c, c ≠ T.root → uφ T e (T.parent c) c + uφ T e c (T.parent c) = if c = e then 1 else 0 := by
  intro c hc
  have h2 : ¬ (T.parent c = e ∧ c = T.parent e) := by
    rintro ⟨h1, h2⟩
    exact no2cycle T he (by rw [← h2, h1])
  unfold uφ
  rw [if_neg h2]
  by_cases hce : c = e
  · subst hce; simp
  · simp [hce]

theorem card_eq_SS (L : List (Fin n)) (P : Fin n → Fin n → Prop) :
    (Finset.univ.filter (fun i : Fin L.length =>
      (i : ℕ) + 1 < L.length ∧ P (T.vertexAt L i) (T.vertexAt L (i + 1)))).card =
      SS T (fun u w => if P u w then 1 else 0) L := by
  rw [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < L.length ∧
    P (T.vertexAt L i) (T.vertexAt L (i + 1)) then 1 else 0)]
  unfold SS
  rcases Nat.eq_zero_or_eq_succ_pred L.length with h | h
  · rw [h]; simp
  · rw [h, Finset.sum_range_succ, Nat.succ_sub_one]
    rw [if_neg (by omega), add_zero]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have : j + 1 < L.length.pred.succ := by omega
    simp only [this, true_and]

theorem card_down (L : List (Fin n)) (e : Fin n) (he : e ≠ T.root) :
    (Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i)).card = SS T (dφ T e) L := by
  have : (Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i)) =
      Finset.univ.filter (fun i : Fin L.length =>
        (i : ℕ) + 1 < L.length ∧ (fun u w => u = T.parent e ∧ w = e)
          (T.vertexAt L i) (T.vertexAt L (i + 1))) := by
    ext i; simp [Tree.DownAt, he]
  rw [this]
  convert card_eq_SS T L (fun u w => u = T.parent e ∧ w = e) using 1
  · congr 1; ext i; simp
  · unfold SS dφ; refine Finset.sum_congr rfl ?_; intro j _; split_ifs <;> simp_all

theorem card_up (L : List (Fin n)) (e : Fin n) (he : e ≠ T.root) :
    (Finset.univ.filter (fun i : Fin L.length => T.UpAt L e i)).card = SS T (uφ T e) L := by
  have : (Finset.univ.filter (fun i : Fin L.length => T.UpAt L e i)) =
      Finset.univ.filter (fun i : Fin L.length =>
        (i : ℕ) + 1 < L.length ∧ (fun u w => u = e ∧ w = T.parent e)
          (T.vertexAt L i) (T.vertexAt L (i + 1))) := by
    ext i; simp [Tree.UpAt, he]
  rw [this]
  convert card_eq_SS T L (fun u w => u = e ∧ w = T.parent e) using 1
  · congr 1; ext i; simp
  · unfold SS uφ; refine Finset.sum_congr rfl ?_; intro j _; split_ifs <;> simp_all

theorem downStep_eq (u w : Fin n) :
    T.downStep u w = ∑ e ∈ T.edges, T.W e * ((dφ T e u w : ℕ) : ℝ) := by
  unfold Tree.downStep
  split_ifs with h
  · rw [Finset.sum_eq_single w]
    · simp [dφ, h.2]
    · intro b _ hb
      simp [dφ, Ne.symm hb]
    · intro hw
      exact absurd (Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ _⟩) hw
  · refine (Finset.sum_eq_zero ?_).symm
    intro e he
    have her : e ≠ T.root := (Finset.mem_erase.mp he).1
    unfold dφ
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩
      subst h2
      exact h ⟨her, h1.symm⟩

theorem dc_eq (L : List (Fin n)) :
    dc T L = ∑ e ∈ T.edges, T.W e * ((SS T (dφ T e) L : ℕ) : ℝ) := by
  unfold dc SS
  simp_rw [downStep_eq T]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [Nat.cast_sum, Finset.mul_sum]

theorem downStep_nonneg (u w : Fin n) : 0 ≤ T.downStep u w := by
  unfold Tree.downStep
  split_ifs with h
  · exact (T.W_pos w h.1).le
  · exact le_refl _

theorem count_dfsS_down (S : Finset (Fin n)) (v e : Fin n) (he : e ≠ T.root) :
    SS T (dφ T e) (dfsS T S v) = if Reach T S v e then 1 else 0 :=
  count_dfsF T S e (dφ T e) (dφ_spec T e he) n v (by have := depth_lt T e; omega)

theorem count_dfsS_up (S : Finset (Fin n)) (v e : Fin n) (he : e ≠ T.root) :
    SS T (uφ T e) (dfsS T S v) = if Reach T S v e then 1 else 0 :=
  count_dfsF T S e (uφ T e) (uφ_spec T e he) n v (by have := depth_lt T e; omega)

theorem reach_ne_root {S : Finset (Fin n)} {v e : Fin n} (h : Reach T S v e) : e ≠ T.root := by
  intro her
  have := reach_depth T S h
  rw [her, T.depth_root] at this
  omega

/-- A reachable edge is crossed downward somewhere in the DFS. -/
theorem dfsS_cross (S : Finset (Fin n)) (v e : Fin n) (h : Reach T S v e) :
    ∃ j, T.CrossAt (dfsS T S v) e j := by
  have he := reach_ne_root T h
  have h1 := count_dfsS_down T S v e he
  rw [if_pos h] at h1
  by_contra hno
  simp only [not_exists] at hno
  have : SS T (dφ T e) (dfsS T S v) = 0 := by
    unfold SS
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finset.mem_range] at hj
    unfold dφ
    rw [if_neg]
    rintro ⟨h2, h3⟩
    exact hno j (Or.inl ⟨he, by omega, h2, h3⟩)
  omega

theorem VB_of_cross_dc (L : List (Fin n)) (e : Fin n) (h : ∃ j, T.CrossAt L e j) :
    VB T L e (dc T L) := by
  refine ⟨Nat.find h, ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩, ?_⟩
  have hlen : Nat.find h + 1 < L.length := by
    rcases Nat.find_spec h with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  unfold Tree.downPrefix dc
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j; simp only [Finset.mem_range]; omega
  · intro j _ _; exact downStep_nonneg T _ _

theorem reach_root (e : Fin n) (he : e ∈ T.edges) : Reach T T.edges T.root e := by
  have her : e ≠ T.root := (Finset.mem_erase.mp he).1
  refine ⟨he, Ne.symm (Ne.symm her), ⟨T.depth e, iter_depth T e⟩, ?_⟩
  intro f hf _ _ _
  exact Finset.mem_erase.mpr ⟨hf, Finset.mem_univ _⟩

theorem dfs_root : T.DFS (dfsS T T.edges T.root) := by
  refine ⟨⟨dfsF_head T _ n _, ?_⟩, dfsF_last T _ n _, ?_⟩
  · exact (isPath_iff T _).mpr (SS_bad_dfsF T _ n _)
  · intro e he
    have her : e ≠ T.root := (Finset.mem_erase.mp he).1
    have hR := reach_root T e he
    refine ⟨?_, ?_⟩
    · rw [card_down T _ e her, count_dfsS_down T _ _ e her, if_pos hR]
    · rw [card_up T _ e her, count_dfsS_up T _ _ e her, if_pos hR]

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## The stubs -/
theorem dfsS_closed (T : Tree n) (S : Finset (Fin n)) (v : Fin n) :
    ClosedAt T v (dfsS T S v) :=
  ⟨dfsF_head T S n v, dfsF_last T S n v, (isPath_iff T _).mpr (SS_bad_dfsF T S n v)⟩

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias dfsS_closed := OnlineTransportation1195.Dev.T31.PartB.dfsS_closed

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dfsS_VB (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) (v e : Fin n)
    (he : Reach T S v e) : VB T (dfsS T S v) e (dc T (dfsS T S v)) :=
  VB_of_cross_dc T _ e (dfsS_cross T S v e he)

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias dfsS_VB := OnlineTransportation1195.Dev.T31.PartB.dfsS_VB

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dfsS_dc (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) (v : Fin n) :
    dc T (dfsS T S v) = ∑ e ∈ T.edges.filter (fun e => Reach T S v e), T.W e := by
  rw [dc_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [count_dfsS_down T S v e (Finset.mem_erase.mp he).1]
  split_ifs <;> simp

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias dfsS_dc := OnlineTransportation1195.Dev.T31.PartB.dfsS_dc

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dfs_exists (T : Tree n) : ∃ L : List (Fin n), T.DFS L :=
  ⟨_, dfs_root T⟩

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias dfs_exists := OnlineTransportation1195.Dev.T31.PartB.dfs_exists

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem equal_case (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (hne : ¬ T.Unequal d) :
    ∃ L : List (Fin n), T.DownDeadlines L d := by
  obtain ⟨hpos, _, hsum⟩ := hD
  have hall : ∀ e ∈ T.edges, ∀ f ∈ T.edges, d e = d f := by
    intro e he f hf
    by_contra h
    exact hne ⟨e, he, f, hf, h⟩
  have hne' : T.edges.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h] at hsum; simp at hsum
  obtain ⟨e0, he0⟩ := hne'
  have hD0 := hpos e0 he0
  have hsumW : ∑ e ∈ T.edges, T.W e = d e0 := by
    have : ∑ e ∈ T.edges, T.W e / d e = (∑ e ∈ T.edges, T.W e) / d e0 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro e he; rw [hall e he e0 he0]
    rw [this, div_eq_one_iff_eq hD0.ne'] at hsum
    exact hsum
  set L := dfsS T T.edges T.root with hL
  have hdc : dc T L = d e0 := by
    rw [hL, dfsS_dc T T.edges (subset_refl _) T.root, ← hsumW]
    congr 1
    exact Finset.filter_true_of_mem (fun e he => reach_root T e he)
  have hVB : ∀ e ∈ T.edges, VB T L e (d e) := by
    intro e he
    have := dfsS_VB T T.edges (subset_refl _) T.root e (reach_root T e he)
    rw [← hL, hdc, hall e0 he0 e he] at this
    exact this
  refine ⟨L, (dfs_root T).1, ?_, hVB⟩
  intro e he
  obtain ⟨i, hi, _⟩ := hVB e he
  exact ⟨i, hi.1⟩

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias equal_case := OnlineTransportation1195.Dev.T31.PartB.equal_case

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartD
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem mem_edges_iff (T : Tree n) (e : Fin n) : e ∈ T.edges ↔ e ≠ T.root := by
  simp [Tree.edges]

theorem downAt_unique (T : Tree n) (L : List (Fin n)) (hL : T.DFS L) (e : Fin n)
    (he : e ∈ T.edges) (i i' : ℕ) (hi : T.DownAt L e i) (hi' : T.DownAt L e i') : i = i' := by
  have h1 := (hL.2.2 e he).1
  have h2 := Finset.card_le_one.mp h1.le ⟨i, by have := hi.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) ⟨i', by have := hi'.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  exact congrArg Fin.val h2

theorem x_spec (T : Tree n) (L : List (Fin n)) (hL : T.DFS L) (e : Fin n) (he : e ∈ T.edges) :
    ∃ i, T.DownAt L e i ∧ T.x L e = T.downPrefix L i := by
  have h1 := (hL.2.2 e he).1
  obtain ⟨⟨i, hi⟩, hmem⟩ : (Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i)).Nonempty :=
    Finset.card_pos.mp (by rw [h1]; norm_num)
  have hdi : T.DownAt L e i := (Finset.mem_filter.mp hmem).2
  unfold Tree.x
  split
  · next j hj =>
    have := List.find?_some hj
    exact ⟨j, by simpa using this, rfl⟩
  · next hj =>
    exfalso
    rw [List.find?_eq_none] at hj
    exact hj i (List.mem_range.mpr hi) (by simpa using hdi)

theorem isAnc_total (T : Tree n) (u u' e : Fin n) (h : T.IsAnc u e) (h' : T.IsAnc u' e) :
    T.IsAnc u u' ∨ T.IsAnc u' u := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨i', rfl⟩ := h'
  rcases le_total i i' with hii | hii
  · right
    refine ⟨i' - i, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hii]
  · left
    refine ⟨i - i', ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hii]

theorem depth_iterate_le (T : Tree n) (k : ℕ) (x : Fin n) :
    T.depth (T.parent^[k] x) ≤ T.depth x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    refine (ih _).trans ?_
    by_cases hx : x = T.root
    · rw [hx, T.parent_root]
    · have := T.depth_parent x hx; omega

theorem depth_lt_of_isAnc (T : Tree n) (a f : Fin n) (h : T.IsAnc a f) (hne : a ≠ f) :
    T.depth a < T.depth f := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => exact absurd rfl hne
  | succ k =>
    have hf : f ≠ T.root := by
      rintro rfl
      apply hne
      rw [Function.iterate_fixed T.parent_root]
    rw [Function.iterate_succ_apply]
    have h1 := depth_iterate_le T k (T.parent f)
    have h2 := T.depth_parent f hf
    omega

/-- Condition for inserting a detour at index `j`. -/
def cond (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) : Prop :=
  0 < j ∧ T.vertexAt L j ∉ T.red d L t ∧ T.vertexAt L j ≠ T.root ∧
    T.DownAt L (T.vertexAt L j) (j - 1)

noncomputable def Dt (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) :
    List (Fin n) :=
  if cond T d L t j then dfsS T (T.red d L t) (T.vertexAt L j) else [T.vertexAt L j]

noncomputable def At (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) :
    Finset (Fin n) :=
  T.edges.filter (fun e => Reach T (T.red d L t) (T.vertexAt L j) e)

theorem red_sub (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    T.red d L t ⊆ T.edges := Finset.filter_subset _ _

theorem Dt_closed (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) :
    ClosedAt T (T.vertexAt L j) (Dt T d L t j) := by
  unfold Dt
  split_ifs
  · exact dfsS_closed _ _ _
  · refine ⟨rfl, rfl, ?_⟩
    intro i hi; simp at hi

theorem dc_Dt (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) :
    dc T (Dt T d L t j) = if cond T d L t j then ∑ e ∈ At T d L t j, T.W e else 0 := by
  unfold Dt At
  split_ifs
  · exact dfsS_dc _ _ (red_sub T d L t) _
  · simp [dc]

theorem sum_dc_le (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (hL : T.DFS L) (t : ℝ)
    (k : ℕ) : ∑ j ∈ Finset.range k, dc T (Dt T d L t j) ≤ T.Rout d L t := by
  simp_rw [dc_Dt]
  rw [← Finset.sum_filter]
  have hdisj : (↑((Finset.range k).filter (cond T d L t)) : Set ℕ).PairwiseDisjoint
      (At T d L t) := by
    intro j hj j' hj' hjj
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hj hj'
    obtain ⟨_, hj0, hjS, hjr, hjD⟩ := hj
    obtain ⟨_, hj0', hjS', hjr', hjD'⟩ := hj'
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    have hR := (Finset.mem_filter.mp he).2
    have hR' := (Finset.mem_filter.mp he').2
    by_cases huu : T.vertexAt L j = T.vertexAt L j'
    · rw [← huu] at hjD'
      have := downAt_unique T L hL _ ((mem_edges_iff T _).mpr hjr) _ _ hjD hjD'
      omega
    · rcases isAnc_total T _ _ e hR.2.2.1 hR'.2.2.1 with h | h
      · exact hjS' (hR.2.2.2 _ hjr' (Ne.symm huu) h hR'.2.2.1)
      · exact hjS (hR'.2.2.2 _ hjr huu h hR.2.2.1)
  rw [← Finset.sum_biUnion hdisj]
  unfold Tree.Rout
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨_, hj0, hjS, hjr, hjD⟩ := Finset.mem_filter.mp hj
    have hR := (Finset.mem_filter.mp he).2
    refine Finset.mem_sdiff.mpr ⟨hR.1, ?_⟩
    intro hP
    exact hjS ((Finset.mem_filter.mp hP).2 _ ((mem_edges_iff T _).mpr hjr) hR.2.2.1)
  · intro e he _
    have : e ≠ T.root :=
      (mem_edges_iff T e).mp (red_sub T d L t (Finset.mem_sdiff.mp he).1)
    exact (T.W_pos e this).le

theorem dc_take (T : Tree n) (L : List (Fin n)) (i : ℕ) (hi : i + 1 < L.length) :
    dc T (L.take (i + 2)) = T.downPrefix L i := by
  unfold dc Tree.downPrefix
  have hlen : (L.take (i + 2)).length - 1 = i + 1 := by simp; omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hv : ∀ m, m < i + 2 → T.vertexAt (L.take (i + 2)) m = T.vertexAt L m := by
    intro m hm
    simp [Tree.vertexAt, List.getD_eq_getElem?_getD, hm]
  rw [hv j (by omega), hv (j + 1) (by omega)]

theorem detour_walk (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (hL : T.DFS L) (t : ℝ) :
    ∃ W : List (Fin n), W.head? = some T.root ∧ IsPath T W ∧
      ∀ e ∈ T.edges, e ∉ T.rootPatch d L t →
        ∃ a ∈ T.edges, T.IsAnc a e ∧ a ∉ T.red d L t ∧
          VB T W e (T.x L a + T.Rout d L t) := by
  have hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (Dt T d L t i) :=
    fun i _ => Dt_closed T d L t i
  refine ⟨blocks L (Dt T d L t), ?_, blocks_isPath T L _ hL.1.2 hD, ?_⟩
  · rw [blocks_head T L _ hD]; exact hL.1.1
  intro e he hnP
  by_cases heS : e ∈ T.red d L t
  · -- red edge with a black ancestor: take the deepest one
    have hB : (T.edges.filter (fun a => T.IsAnc a e ∧ a ∉ T.red d L t)).Nonempty := by
      by_contra hne
      apply hnP
      refine Finset.mem_filter.mpr ⟨heS, ?_⟩
      intro a ha hae
      by_contra haS
      exact hne ⟨a, Finset.mem_filter.mpr ⟨ha, hae, haS⟩⟩
    obtain ⟨a, haB, hamax⟩ := Finset.exists_max_image _ T.depth hB
    obtain ⟨ha, hae, haS⟩ := Finset.mem_filter.mp haB
    have har : a ≠ T.root := (mem_edges_iff T a).mp ha
    have hReach : Reach T (T.red d L t) a e := by
      refine ⟨heS, ?_, hae, ?_⟩
      · rintro rfl; exact haS heS
      · intro f hfr hfa haf hfe
        by_contra hfS
        have h1 := hamax f (Finset.mem_filter.mpr ⟨(mem_edges_iff T f).mpr hfr, hfe, hfS⟩)
        have h2 := depth_lt_of_isAnc T a f haf (Ne.symm hfa)
        omega
    obtain ⟨i, hDi, hxi⟩ := x_spec T L hL a ha
    have hva : T.vertexAt L (i + 1) = a := hDi.2.2.2
    have hcond : cond T d L t (i + 1) := by
      refine ⟨Nat.succ_pos _, ?_, ?_, ?_⟩
      · rw [hva]; exact haS
      · rw [hva]; exact har
      · rw [hva]; simpa using hDi
    have hDeq : Dt T d L t (i + 1) = dfsS T (T.red d L t) a := by
      unfold Dt; rw [if_pos hcond, hva]
    have hV := dfsS_VB T (T.red d L t) (red_sub T d L t) a e hReach
    rw [← hDeq] at hV
    have hB2 := blocks_VB T L _ hD (i + 1) hDi.2.1 e _ hV
    refine ⟨a, ha, hae, haS, VB_mono T _ e _ _ hB2 ?_⟩
    rw [dc_take T L i hDi.2.1, ← hxi, add_assoc, ← Finset.sum_range_succ]
    have := sum_dc_le T d L hL t (i + 1 + 1)
    linarith
  · -- black edge
    obtain ⟨i, hDi, hxi⟩ := x_spec T L hL e he
    obtain ⟨p, hp, hp1, hp2, hpc⟩ := blocks_step T L _ hD i hDi.2.1
    refine ⟨e, he, ⟨0, rfl⟩, heS, ?_⟩
    refine VB_of_cross T _ e p _ (Or.inl ⟨hDi.1, hp, ?_, ?_⟩) ?_
    · rw [hp1]; exact hDi.2.2.1
    · rw [hp2]; exact hDi.2.2.2
    · rw [hpc, hxi]
      have := sum_dc_le T d L hL t (i + 1)
      linarith

end OnlineTransportation1195.Dev.T31.PartD
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## The patch-detour walk (Part D) -/
alias detour_walk := OnlineTransportation1195.Dev.T31.PartD.detour_walk

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartC
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## The subtree on a parent-closed vertex set -/
noncomputable def embV (V : Finset (Fin n)) (i : Fin V.card) : Fin n := (V.equivFin.symm i).1

noncomputable def backV (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (v : Fin n) :
    Fin V.card :=
  if hv : v ∈ V then V.equivFin ⟨v, hv⟩ else V.equivFin ⟨T.root, hr⟩

theorem embV_mem (V : Finset (Fin n)) (i : Fin V.card) : embV V i ∈ V :=
  (V.equivFin.symm i).2

theorem embV_backV (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (v : Fin n)
    (hv : v ∈ V) : embV V (backV T V hr v) = v := by
  simp [embV, backV, hv]

theorem backV_embV (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (i : Fin V.card) :
    backV T V hr (embV V i) = i := by
  simp [embV, backV]

theorem embV_inj (V : Finset (Fin n)) : Function.Injective (embV V) := by
  intro a b h
  exact V.equivFin.symm.injective (Subtype.ext h)

noncomputable def subT (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V)
    (hp : ∀ v ∈ V, T.parent v ∈ V) : Tree V.card where
  root := backV T V hr T.root
  parent := fun i => backV T V hr (T.parent (embV V i))
  depth := fun i => T.depth (embV V i)
  parent_root := by
    simp only [embV_backV T V hr _ hr, T.parent_root]
  depth_root := by
    simp only [embV_backV T V hr _ hr, T.depth_root]
  depth_parent := by
    intro v hv
    have hne : embV V v ≠ T.root := fun h => hv (by rw [← h, backV_embV])
    simp only [embV_backV T V hr _ (hp _ (embV_mem V v))]
    exact T.depth_parent _ hne
  W := fun i => T.W (embV V i)
  W_pos := by
    intro v hv
    have hne : embV V v ≠ T.root := fun h => hv (by rw [← h, backV_embV])
    exact T.W_pos _ hne

end OnlineTransportation1195.Dev.T31.PartC
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartC
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (hp : ∀ v ∈ V, T.parent v ∈ V)
theorem emb_root : embV V (subT T V hr hp).root = T.root := embV_backV T V hr _ hr

theorem emb_parent (i : Fin V.card) :
    embV V ((subT T V hr hp).parent i) = T.parent (embV V i) :=
  embV_backV T V hr _ (hp _ (embV_mem V i))

theorem emb_eq_root_iff (i : Fin V.card) :
    embV V i = T.root ↔ i = (subT T V hr hp).root := by
  rw [← emb_root T V hr hp]; exact (embV_inj V).eq_iff

theorem emb_parent_iff (u v : Fin V.card) :
    (subT T V hr hp).parent v = u ↔ T.parent (embV V v) = embV V u := by
  rw [← emb_parent T V hr hp]; exact (embV_inj V).eq_iff.symm

theorem emb_iterate (k : ℕ) (b : Fin V.card) :
    embV V ((subT T V hr hp).parent^[k] b) = T.parent^[k] (embV V b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', emb_parent, ih]

theorem emb_isAnc (a b : Fin V.card) :
    (subT T V hr hp).IsAnc a b ↔ T.IsAnc (embV V a) (embV V b) := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [← emb_iterate T V hr hp, hk]⟩
  · rintro ⟨k, hk⟩; exact ⟨k, embV_inj V (by rw [emb_iterate T V hr hp, hk])⟩

theorem emb_vertexAt (L : List (Fin V.card)) (j : ℕ) :
    T.vertexAt (L.map (embV V)) j = embV V ((subT T V hr hp).vertexAt L j) := by
  unfold Tree.vertexAt
  rw [← emb_root T V hr hp, List.getD_map]

theorem emb_downStep (u v : Fin V.card) :
    T.downStep (embV V u) (embV V v) = (subT T V hr hp).downStep u v := by
  unfold Tree.downStep
  simp only [Ne, emb_eq_root_iff T V hr hp, ← emb_parent_iff T V hr hp]
  rfl

theorem emb_adj (u v : Fin V.card) :
    (subT T V hr hp).Adj u v ↔ T.Adj (embV V u) (embV V v) := by
  unfold Tree.Adj
  simp only [Ne, emb_eq_root_iff T V hr hp, ← emb_parent_iff T V hr hp]

theorem emb_downPrefix (L : List (Fin V.card)) (i : ℕ) :
    T.downPrefix (L.map (embV V)) i = (subT T V hr hp).downPrefix L i := by
  unfold Tree.downPrefix
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [emb_vertexAt T V hr hp, emb_vertexAt T V hr hp, emb_downStep]

theorem emb_downAt (L : List (Fin V.card)) (e : Fin V.card) (i : ℕ) :
    T.DownAt (L.map (embV V)) (embV V e) i ↔ (subT T V hr hp).DownAt L e i := by
  unfold Tree.DownAt
  rw [List.length_map, emb_vertexAt T V hr hp, emb_vertexAt T V hr hp, ← emb_parent T V hr hp,
    (embV_inj V).eq_iff, (embV_inj V).eq_iff, Ne, emb_eq_root_iff T V hr hp]

theorem emb_upAt (L : List (Fin V.card)) (e : Fin V.card) (i : ℕ) :
    T.UpAt (L.map (embV V)) (embV V e) i ↔ (subT T V hr hp).UpAt L e i := by
  unfold Tree.UpAt
  rw [List.length_map, emb_vertexAt T V hr hp, emb_vertexAt T V hr hp, ← emb_parent T V hr hp,
    (embV_inj V).eq_iff, (embV_inj V).eq_iff, Ne, emb_eq_root_iff T V hr hp]

theorem emb_crossAt (L : List (Fin V.card)) (e : Fin V.card) (i : ℕ) :
    T.CrossAt (L.map (embV V)) (embV V e) i ↔ (subT T V hr hp).CrossAt L e i := by
  unfold Tree.CrossAt
  rw [emb_downAt, emb_upAt]

theorem emb_firstAt (L : List (Fin V.card)) (e : Fin V.card) (i : ℕ) :
    T.FirstAt (L.map (embV V)) (embV V e) i ↔ (subT T V hr hp).FirstAt L e i := by
  unfold Tree.FirstAt
  simp only [emb_crossAt T V hr hp]

theorem mem_edges_iff (i : Fin V.card) :
    i ∈ (subT T V hr hp).edges ↔ embV V i ≠ T.root := by
  rw [Ne, emb_eq_root_iff T V hr hp]
  exact ⟨fun h => (Finset.mem_erase.mp h).1,
    fun h => Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩

end OnlineTransportation1195.Dev.T31.PartC
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartC
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## Truncation -/
theorem vertexAt_take (T : Tree n) (L : List (Fin n)) (k j : ℕ) (hj : j < k) :
    T.vertexAt (L.take k) j = T.vertexAt L j := by
  unfold Tree.vertexAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj]

theorem crossAt_take (T : Tree n) (L : List (Fin n)) (k : ℕ) (e : Fin n) (j : ℕ) :
    T.CrossAt (L.take k) e j ↔ T.CrossAt L e j ∧ j + 1 < k := by
  unfold Tree.CrossAt Tree.DownAt Tree.UpAt
  constructor
  · intro h
    have hlen : j + 1 < (L.take k).length := by rcases h with h | h <;> exact h.2.1
    rw [List.length_take] at hlen
    have hk : j + 1 < k := by omega
    rw [vertexAt_take T L k j (by omega), vertexAt_take T L k (j + 1) hk] at h
    refine ⟨?_, hk⟩
    rcases h with h | h
    · exact Or.inl ⟨h.1, by omega, h.2.2⟩
    · exact Or.inr ⟨h.1, by omega, h.2.2⟩
  · rintro ⟨h, hk⟩
    have hlen : j + 1 < L.length := by rcases h with h | h <;> exact h.2.1
    rw [vertexAt_take T L k j (by omega), vertexAt_take T L k (j + 1) hk, List.length_take]
    rcases h with h | h
    · exact Or.inl ⟨h.1, by omega, h.2.2⟩
    · exact Or.inr ⟨h.1, by omega, h.2.2⟩

theorem downPrefix_take (T : Tree n) (L : List (Fin n)) (k i : ℕ) (hi : i + 1 < k) :
    T.downPrefix (L.take k) i = T.downPrefix L i := by
  unfold Tree.downPrefix
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [vertexAt_take T L k j (by omega), vertexAt_take T L k (j + 1) (by omega)]

/-! ## The stub -/
theorem subtree_walk
    (hIH : ∀ m < n, ∀ (T' : Tree m) (d' : Fin m → ℝ), T'.Normalized d' →
      ∃ L, T'.DownDeadlines L d')
    (T : Tree n) (P : Finset (Fin n)) (hP : P ⊆ T.edges) (hne : P.Nonempty)
    (hlt : P.card + 1 < n)
    (hup : ∀ e ∈ P, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ P)
    (dP : Fin n → ℝ) (hpos : ∀ e ∈ P, 0 < dP e)
    (hmono : ∀ a ∈ P, ∀ b ∈ P, T.IsAnc a b → dP a ≤ dP b)
    (hsum : ∑ e ∈ P, T.W e / dP e = 1) (s : ℝ) (hs : ∀ e ∈ P, dP e ≤ s) :
    ∃ M : List (Fin n), M.head? = some T.root ∧ IsPath T M ∧
      (∀ e ∈ P, VB T M e (dP e)) ∧ dc T M ≤ s := by
  have hr : T.root ∈ insert T.root P := Finset.mem_insert_self _ _
  have hrP : T.root ∉ P := fun h => by have := hP h; simp [Tree.edges] at this
  have hPne : ∀ e ∈ P, e ≠ T.root := fun e he h => hrP (h ▸ he)
  have hp : ∀ v ∈ insert T.root P, T.parent v ∈ insert T.root P := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvP
    · rw [T.parent_root]; exact hr
    · by_cases h : T.parent v = T.root
      · rw [h]; exact hr
      · apply Finset.mem_insert_of_mem
        exact hup v hvP _ (by simp [Tree.edges, h]) ⟨1, rfl⟩
  have hcard : (insert T.root P).card = P.card + 1 := Finset.card_insert_of_notMem hrP
  have hlt' : (insert T.root P).card < n := by omega
  have hmemP : ∀ i, i ∈ (subT T _ hr hp).edges ↔ embV _ i ∈ P := by
    intro i
    rw [mem_edges_iff]
    constructor
    · intro h
      rcases Finset.mem_insert.mp (embV_mem _ i) with h' | h'
      · exact absurd h' h
      · exact h'
    · exact hPne _
  have hedges : (subT T _ hr hp).edges.map ⟨embV _, embV_inj _⟩ = P := by
    ext e
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact (hmemP i).mp hi
    · intro he
      refine ⟨backV T _ hr e, (hmemP _).mpr ?_, ?_⟩ <;>
        rw [embV_backV T _ hr e (Finset.mem_insert_of_mem he)]
      exact he
  have hnorm : (subT T _ hr hp).Normalized (fun i => dP (embV _ i)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; exact hpos _ ((hmemP i).mp hi)
    · intro a ha b hb hab
      exact hmono _ ((hmemP a).mp ha) _ ((hmemP b).mp hb) ((emb_isAnc T _ hr hp a b).mp hab)
    · have h2 := Finset.sum_map (subT T _ hr hp).edges ⟨embV _, embV_inj _⟩
        (fun e => T.W e / dP e)
      rw [hedges] at h2
      exact h2.symm.trans hsum
  obtain ⟨L', hW, -, hDL⟩ := hIH _ hlt' _ _ hnorm
  have hF : ∀ e ∈ P, ∃ i, T.FirstAt (L'.map (embV _)) e i ∧
      T.downPrefix (L'.map (embV _)) i ≤ dP e := by
    intro e he
    have heV : e ∈ insert T.root P := Finset.mem_insert_of_mem he
    have hb : backV T _ hr e ∈ (subT T _ hr hp).edges := by
      rw [hmemP, embV_backV T _ hr e heV]; exact he
    obtain ⟨i, hi, hc⟩ := hDL _ hb
    refine ⟨i, ?_, ?_⟩
    · have := (emb_firstAt T _ hr hp L' _ i).mpr hi
      rwa [embV_backV T _ hr e heV] at this
    · rw [emb_downPrefix T _ hr hp]
      simpa only [embV_backV T _ hr e heV] using hc
  choose! f hf using hF
  obtain ⟨e0, he0, hmax⟩ := P.exists_max_image f hne
  set L := L'.map (embV (insert T.root P)) with hLdef
  have hL0 : f e0 + 1 < L.length := by
    rcases (hf e0 he0).1.1 with h | h <;> exact h.2.1
  have hlenM : (L.take (f e0 + 2)).length = f e0 + 2 := by
    rw [List.length_take]; omega
  refine ⟨L.take (f e0 + 2), ?_, ?_, ?_, ?_⟩
  · have hh : L.head? = some T.root := by
      rw [hLdef, List.head?_map, hW.1, Option.map_some, emb_root]
    rw [List.head?_take, if_neg (by omega), hh]
  · intro i hi
    rw [hlenM] at hi
    rw [vertexAt_take T L _ i (by omega), vertexAt_take T L _ (i + 1) hi]
    have hi' : i + 1 < L'.length := by rw [hLdef, List.length_map] at hL0; omega
    have := hW.2 i hi'
    rw [emb_adj T _ hr hp, ← emb_vertexAt T _ hr hp, ← emb_vertexAt T _ hr hp] at this
    exact this
  · intro e he
    have hfe : f e ≤ f e0 := hmax e he
    refine ⟨f e, ⟨(crossAt_take T L _ e _).mpr ⟨(hf e he).1.1, by omega⟩, ?_⟩, ?_⟩
    · intro j hj hc
      exact (hf e he).1.2 j hj ((crossAt_take T L _ e _).mp hc).1
    · rw [downPrefix_take T L _ _ (by omega)]; exact (hf e he).2
  · have : dc T (L.take (f e0 + 2)) = T.downPrefix (L.take (f e0 + 2)) (f e0) := by
      unfold dc Tree.downPrefix
      rw [hlenM, show f e0 + 2 - 1 = f e0 + 1 by omega]
    rw [this, downPrefix_take T L _ _ (by omega)]
    exact ((hf e0 he0).2).trans (hs e0 he0)

end OnlineTransportation1195.Dev.T31.PartC
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## The root patch as a smaller tree (Part C) -/
alias subtree_walk := OnlineTransportation1195.Dev.T31.PartC.subtree_walk

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem mem_edges_iff (T : Tree n) (e : Fin n) : e ∈ T.edges ↔ e ≠ T.root := by
  simp [Tree.edges]

theorem W_nonneg_of_mem (T : Tree n) (e : Fin n) (he : e ∈ T.edges) : 0 ≤ T.W e :=
  (T.W_pos e ((mem_edges_iff T e).mp he)).le

theorem F_le_self (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (t : ℝ) (ht : 0 ≤ t) :
    T.F d t ≤ t := by
  unfold Tree.F
  calc ∑ e ∈ T.edges, T.W e * min 1 (t / d e)
      ≤ ∑ e ∈ T.edges, T.W e * (t / d e) := by
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (W_nonneg_of_mem T e he)
    _ = ∑ e ∈ T.edges, t * (T.W e / d e) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
    _ = t * ∑ e ∈ T.edges, T.W e / d e := (Finset.mul_sum _ _ _).symm
    _ = t := by rw [hD.2.2, mul_one]

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## Real-analysis facts (Part E) -/
alias F_le_self := OnlineTransportation1195.Dev.T31.PartE.F_le_self

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem F_le_total (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (t : ℝ) :
    T.F d t ≤ ∑ e ∈ T.edges, T.W e := by
  unfold Tree.F
  apply Finset.sum_le_sum
  intro e he
  calc T.W e * min 1 (t / d e) ≤ T.W e * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (W_nonneg_of_mem T e he)
    _ = T.W e := mul_one _

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias F_le_total := OnlineTransportation1195.Dev.T31.PartE.F_le_total

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem F_continuous (T : Tree n) (d : Fin n → ℝ) : Continuous (fun s => T.F d s) := by
  unfold Tree.F
  apply continuous_finsetSum
  intro e _
  exact continuous_const.mul (continuous_const.min (continuous_id.div_const _))

theorem F_zero (T : Tree n) (d : Fin n → ℝ) : T.F d 0 = 0 := by
  simp [Tree.F]

theorem exists_s (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (r t : ℝ) (ht : 0 < t)
    (hr : 0 < r) (hrt : r < T.F d t) : ∃ s, 0 < s ∧ s ≤ t ∧ T.F d s = r := by
  have hsub := intermediate_value_Icc ht.le (F_continuous T d).continuousOn
  have hmem : r ∈ Set.Icc (T.F d 0) (T.F d t) := by
    rw [F_zero]; exact ⟨hr.le, hrt.le⟩
  obtain ⟨s, ⟨hs0, hst⟩, hFs⟩ := hsub hmem
  refine ⟨s, ?_, hst, hFs⟩
  rcases hs0.lt_or_eq with h | h
  · exact h
  · subst h
    have h0 : T.F d 0 = r := hFs
    rw [F_zero] at h0; linarith

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias exists_s := OnlineTransportation1195.Dev.T31.PartE.exists_s

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem R_eq (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    T.R d L t = T.Rin d L t + T.Rout d L t := by
  have hsub : T.rootPatch d L t ⊆ T.red d L t := Finset.filter_subset _ _
  have := Finset.sum_sdiff (f := T.W) hsub
  unfold Tree.R Tree.Rin Tree.Rout
  linarith

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias R_eq := OnlineTransportation1195.Dev.T31.PartE.R_eq

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem Rout_nonneg (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    0 ≤ T.Rout d L t := by
  unfold Tree.Rout
  apply Finset.sum_nonneg
  intro e he
  have he1 : e ∈ T.red d L t := (Finset.mem_sdiff.mp he).1
  exact W_nonneg_of_mem T e (Finset.mem_filter.mp he1).1

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias Rout_nonneg := OnlineTransportation1195.Dev.T31.PartE.Rout_nonneg

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem Rin_pos (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ)
    (h : (T.rootPatch d L t).Nonempty) : 0 < T.Rin d L t := by
  unfold Tree.Rin
  apply Finset.sum_pos _ h
  intro e he
  have he1 : e ∈ T.red d L t := (Finset.mem_filter.mp he).1
  exact T.W_pos e ((mem_edges_iff T e).mp (Finset.mem_filter.mp he1).1)

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias Rin_pos := OnlineTransportation1195.Dev.T31.PartE.Rin_pos

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem isAnc_trans (T : Tree n) (a b c : Fin n) (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) :
    T.IsAnc a c := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias isAnc_trans := OnlineTransportation1195.Dev.T31.PartE.isAnc_trans

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem edges_card (T : Tree n) : T.edges.card = n - 1 := by
  unfold Tree.edges
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias edges_card := OnlineTransportation1195.Dev.T31.PartE.edges_card

/-! ## Assembly -/
theorem main_step (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d)
    (hIH : ∀ m < n, ∀ (T' : Tree m) (d' : Fin m → ℝ), T'.Normalized d' →
      ∃ L, T'.DownDeadlines L d') :
    ∃ L : List (Fin n), T.DownDeadlines L d := by
  by_cases hU : T.Unequal d
  swap
  · exact equal_case T d hD hU
  obtain ⟨L, hL⟩ := dfs_exists T
  obtain ⟨t, ht, hRF⟩ := strict_red_weight_budget T d L hD hL hU
  set P := T.rootPatch d L t with hPdef
  have hPsub : P ⊆ T.edges := fun e he =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
  -- the root-patch walk M with budget `dc M + Rout ≤ t`
  have hM : ∃ M : List (Fin n), M.head? = some T.root ∧ IsPath T M ∧
      (∀ e ∈ P, VB T M e (d e)) ∧ dc T M + T.Rout d L t ≤ t := by
    by_cases hPe : P.Nonempty
    · have hRin := Rin_pos T d L t hPe
      have hReq := R_eq T d L t
      have hRo := Rout_nonneg T d L t
      obtain ⟨s, hs0, hst, hFs⟩ := exists_s T d hD (T.Rin d L t) t ht hRin (by linarith)
      have hnorm : T.patchNormalization d L s t = 1 :=
        (root_patch_normalization_iff T d L hD hL s t ht hs0 hst).mpr hFs.symm
      have hbud : s + T.Rout d L t ≤ t :=
        detour_budget_inequality T d L hD hL s t ht hs0 hst hFs.symm hRF.le
      have hPne : P ≠ T.edges := by
        intro hPE
        have h1 : T.Rin d L t = ∑ e ∈ T.edges, T.W e := by
          unfold Tree.Rin; rw [← hPdef, hPE]
        have h2 := F_le_total T d hD t
        linarith
      have hlt : P.card + 1 < n := by
        have h1 : P.card < T.edges.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hPsub, hPne⟩)
        rw [edges_card] at h1
        omega
      have hup : ∀ e ∈ P, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ P := by
        intro e he a ha hae
        have he' := Finset.mem_filter.mp he
        refine Finset.mem_filter.mpr ⟨he'.2 a ha hae, ?_⟩
        intro b hb hba
        exact he'.2 b hb (isAnc_trans T b a e hba hae)
      obtain ⟨M, hMh, hMp, hMV, hMc⟩ := subtree_walk hIH T P hPsub hPe hlt hup
        (fun e => min (d e) s)
        (fun e he => lt_min (hD.1 e (hPsub he)) hs0)
        (fun a ha b hb hab => min_le_min_right s (hD.2.1 a (hPsub ha) b (hPsub hb) hab))
        hnorm s (fun e _ => min_le_right _ _)
      refine ⟨M, hMh, hMp, fun e he => VB_mono T M e _ _ (hMV e he) (min_le_left _ _), ?_⟩
      linarith
    · refine ⟨[T.root], rfl, ?_, ?_, ?_⟩
      · intro i hi; simp at hi
      · intro e he; exact absurd ⟨e, he⟩ hPe
      · have hP0 : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPe
        have hReq := R_eq T d L t
        have hRin0 : T.Rin d L t = 0 := by
          unfold Tree.Rin; rw [← hPdef, hP0]; simp
        have hF := F_le_self T d hD t ht.le
        have hdc : dc T [T.root] = 0 := by simp [dc]
        rw [hdc]
        linarith
  obtain ⟨M, hMh, hMp, hMV, hMb⟩ := hM
  have hMne : M ≠ [] := by rintro rfl; simp at hMh
  obtain ⟨W, hWh, hWp, hWV⟩ := detour_walk T d L hL t
  obtain ⟨v, hv⟩ : ∃ v, M.getLast? = some v := by
    cases h : M.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hMne
    | some v => exact ⟨v, rfl⟩
  obtain ⟨U, hUh, hUl, hUp, hUc⟩ := up_path T v
  have hMU : U.head? = M.getLast? := by rw [hUh, hv]
  set MU := M ++ U.tail with hMUdef
  have hMUne : MU ≠ [] := by simp [hMUdef, hMne]
  have hMUl : MU.getLast? = some T.root := by
    rw [hMUdef, getLast_append_tail M U hMne hMU, hUl]
  have hWMU : W.head? = MU.getLast? := by rw [hWh, hMUl]
  have hMUp : IsPath T MU := isPath_append T M U hMp hUp hMU
  have hMUc : dc T MU = dc T M := by
    rw [hMUdef, dc_append T M U hMne hMU, hUc, add_zero]
  have hMUh : MU.head? = some T.root := by rw [hMUdef, head_append M _ hMne, hMh]
  -- all deadlines
  have hall : ∀ e ∈ T.edges, VB T (MU ++ W.tail) e (d e) := by
    intro e he
    by_cases heP : e ∈ P
    · exact VB_append_left T MU W.tail e _ (VB_append_left T M U.tail e _ (hMV e heP))
    · obtain ⟨a, ha, hae, hared, hVa⟩ := hWV e he heP
      have h1 := VB_append_right T MU W e _ hMUne hWMU hVa
      refine VB_mono T _ e _ _ h1 ?_
      have hxa : T.x L a + t ≤ d a := by
        by_contra hc
        exact hared (Finset.mem_filter.mpr ⟨ha, not_le.mp hc⟩)
      have hda : d a ≤ d e := hD.2.1 a ha e he hae
      rw [hMUc]
      linarith
  refine ⟨MU ++ W.tail, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [head_append MU _ hMUne, hMUh]
  · exact isPath_append T MU W hMUp hWp hWMU
  · intro e he
    obtain ⟨i, hi, _⟩ := hall e he
    exact ⟨i, hi.1⟩
  · intro e he
    exact hall e he

theorem main : ∀ (n : ℕ) (T : Tree n) (d : Fin n → ℝ), T.Normalized d →
    ∃ L : List (Fin n), T.DownDeadlines L d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T d hD
    exact main_step T d hD (fun m hm T' d' hd' => ih m hm T' d' hd')

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Main
theorem chk_normalized_downward_deadlines {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (hD : T.Normalized d) :
    ∃ L : List (Fin n), T.DownDeadlines L d :=
  OnlineTransportation1195.Dev.T31.main n T d hD

end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_normalized_downward_deadlines := @OnlineTransportation1195.Main.chk_normalized_downward_deadlines
