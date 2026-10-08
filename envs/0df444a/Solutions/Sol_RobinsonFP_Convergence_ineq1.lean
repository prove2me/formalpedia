-- Prove2me | solution 1 for RobinsonFP.Convergence.ineq1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:36:43.877598+00:00
-- url     : https://prove2.me/submissions/d502a733-1dff-462e-a6c2-dc483cdc05e7

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem rb_le_vmax [Nonempty ι] (w : ι → ℝ) (i : ι) : w i ≤ vmax w :=
  Finset.le_sup' w (Finset.mem_univ i)

theorem rb_vmax_le [Nonempty ι] {w : ι → ℝ} {c : ℝ} (h : ∀ i, w i ≤ c) : vmax w ≤ c :=
  Finset.sup'_le _ _ (fun i _ => h i)

theorem rb_vmin_le [Nonempty ι] (w : ι → ℝ) (i : ι) : vmin w ≤ w i :=
  Finset.inf'_le w (Finset.mem_univ i)

theorem rb_le_vmin [Nonempty ι] {w : ι → ℝ} {c : ℝ} (h : ∀ i, c ≤ w i) : c ≤ vmin w :=
  Finset.le_inf' _ _ (fun i _ => h i)

theorem rb_exists_eq_vmax [Nonempty ι] (w : ι → ℝ) : ∃ i, w i = vmax w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) w
  exact ⟨i, hi.symm⟩

theorem rb_exists_eq_vmin [Nonempty ι] (w : ι → ℝ) : ∃ i, w i = vmin w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) w
  exact ⟨i, hi.symm⟩

theorem rb_vmax_neg [Nonempty ι] (w : ι → ℝ) : vmax (fun i => - w i) = - vmin w := by
  apply le_antisymm
  · apply rb_vmax_le
    intro i
    have := rb_vmin_le w i
    linarith
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmin w
    have := rb_le_vmax (fun i => - w i) i
    linarith

theorem rb_vmin_neg [Nonempty ι] (w : ι → ℝ) : vmin (fun i => - w i) = - vmax w := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmax w
    have := rb_vmin_le (fun i => - w i) i
    linarith
  · apply rb_le_vmin
    intro i
    have := rb_le_vmax w i
    linarith

theorem rb_gap_step [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (t : ℕ) :
    vmax (V t) - vmin (U t) ≤ vmax (V (t + 1)) - vmin (U (t + 1)) := by
  obtain ⟨i, j, hi, hj, hU, hV⟩ := h.2 t
  have e1 : V (t + 1) i = V t i + A i j := by simpa using congrFun hV i
  have e2 : U (t + 1) j = U t j + A i j := by simpa using congrFun hU j
  have h1 := rb_le_vmax (V (t + 1)) i
  have h2 := rb_vmin_le (U (t + 1)) j
  linarith

theorem rb_gap_mono [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) :
    Monotone (fun t => vmax (V t) - vmin (U t)) :=
  monotone_nat_of_le_succ (fun t => rb_gap_step h t)

theorem rb_gap_nonneg [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (t : ℕ) :
    0 ≤ vmax (V t) - vmin (U t) := by
  have := rb_gap_mono h (Nat.zero_le t)
  have h0 : vmax (V 0) - vmin (U 0) = 0 := by rw [h.1]; ring
  simp only at this
  linarith
theorem rb_ineq1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∀ x ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ κ,
      vmin (fun j => ∑ i, A i j * x i) ≤ vmax (fun i => ∑ j, A i j * y j) := by
  intro x hx y hy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  calc vmin (fun j => ∑ i, A i j * x i) = ∑ j, y j * vmin (fun j => ∑ i, A i j * x i) := by
        rw [← Finset.sum_mul, hy1, one_mul]
    _ ≤ ∑ j, y j * (∑ i, A i j * x i) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (rb_vmin_le (fun j => ∑ i, A i j * x i) j) (hy0 j)
    _ = ∑ j, ∑ i, y j * (A i j * x i) := by simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, y j * (A i j * x i) := Finset.sum_comm
    _ = ∑ i, x i * (∑ j, A i j * y j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
    _ ≤ ∑ i, x i * vmax (fun i => ∑ j, A i j * y j) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (rb_le_vmax (fun i => ∑ j, A i j * y j) i) (hx0 i)
    _ = vmax (fun i => ∑ j, A i j * y j) := by rw [← Finset.sum_mul, hx1, one_mul]

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) :
    ∀ x ∈ stdSimplex ℝ ι, ∀ y ∈ stdSimplex ℝ κ,
      vmin (fun j => ∑ i, A i j * x i) ≤ vmax (fun i => ∑ j, A i j * y j) := by
  exact rb_ineq1 A
