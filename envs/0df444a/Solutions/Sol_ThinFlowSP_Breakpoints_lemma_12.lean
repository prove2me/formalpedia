-- Prove2me | solution 1 for ThinFlowSP.Breakpoints.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:34:32.465842+00:00
-- url     : https://prove2.me/submissions/2bafc5dc-9fcf-48a7-bb40-1e6e91e1a005

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network

namespace ThinFlowSP.Breakpoints

/-- A weakly column diagonally dominant real matrix has non-negative determinant. -/
theorem det_nonneg_of_col_dominant {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n ℝ)
    (h : ∀ k, ∑ i ∈ Finset.univ.erase k, |N i k| ≤ N k k) : 0 ≤ N.det := by
  have hdiag : ∀ k, 0 ≤ N k k := fun k =>
    le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (h k)
  -- strict dominance of `s • N + t • 1`
  have hne : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 < t → (s • N + t • (1 : Matrix n n ℝ)).det ≠ 0 := by
    intro s hs t ht
    apply det_ne_zero_of_sum_col_lt_diag
    intro k
    have e1 : ∀ i ∈ Finset.univ.erase k, ‖(s • N + t • (1 : Matrix n n ℝ)) i k‖ = s * |N i k| := by
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [Matrix.one_apply, hik, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1]
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ‖(s • N + t • (1 : Matrix n n ℝ)) k k‖ = s * N k k + t := by
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Real.norm_eq_abs]
      exact abs_of_nonneg (by have := mul_nonneg hs.1 (hdiag k); linarith)
    rw [e2]
    have := mul_le_mul_of_nonneg_left (h k) hs.1
    linarith
  -- positivity of `det (N + t • 1)` for `t > 0`
  have hpos : ∀ t : ℝ, 0 < t → 0 < (N + t • (1 : Matrix n n ℝ)).det := by
    intro t ht
    by_contra hle
    push Not at hle
    let g : ℝ → ℝ := fun s => (s • N + t • (1 : Matrix n n ℝ)).det
    have gc : Continuous g := by
      apply Continuous.matrix_det
      fun_prop
    have g0 : 0 < g 0 := by
      simp only [g, zero_smul, zero_add, Matrix.det_smul, Matrix.det_one, mul_one]
      positivity
    have g1 : g 1 ≤ 0 := by simpa [g] using hle
    obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' (zero_le_one' ℝ) gc.continuousOn
      ⟨g1, g0.le⟩
    exact hne s hs t ht hgs
  -- limit `t → 0⁺`
  let f : ℝ → ℝ := fun t => (N + t • (1 : Matrix n n ℝ)).det
  have fc : Continuous f := by
    apply Continuous.matrix_det
    fun_prop
  have hlim : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
    (fc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hf0 : f 0 = N.det := by simp [f]
  rw [← hf0]
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hpos t ht).le

theorem lem12 (G : Net) (ν : G.A → ℝ) (hν : ∀ a, 0 < ν a) (U : Finset G.V) :
    0 ≤ ((laplacian G ν).submatrix (fun i : U => i.1) (fun i : U => i.1)).det := by
  apply det_nonneg_of_col_dominant
  intro k
  simp only [Matrix.submatrix_apply]
  have hkk : laplacian G ν k.1 k.1 = ∑ a ∈ Finset.univ.filter (fun a => G.head a = k.1), ν a := by
    simp [laplacian]
  have hoff : ∀ i ∈ (Finset.univ : Finset U).erase k, |laplacian G ν i.1 k.1| =
      ∑ a, if G.tail a = i.1 ∧ G.head a = k.1 then ν a else 0 := by
    intro i hi
    have hik : i.1 ≠ k.1 := fun e => Finset.ne_of_mem_erase hi (Subtype.ext e)
    simp only [laplacian, Matrix.of_apply, hik, if_false, abs_neg]
    rw [abs_of_nonneg (Finset.sum_nonneg fun a _ => (hν a).le), Finset.sum_filter]
  rw [Finset.sum_congr rfl hoff, Finset.sum_comm, hkk, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a _
  by_cases hh : G.head a = k.1
  · simp only [hh, and_true, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ : Finset U).erase k |>.filter (fun i : U => G.tail a = i.1)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact Subtype.ext ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
    have := (hν a).le
    have : (((Finset.univ : Finset U).erase k |>.filter (fun i : U => G.tail a = i.1)).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith
  · simp [hh]

end ThinFlowSP.Breakpoints

open ThinFlowSP.Breakpoints in
theorem solution (G : Net) (ν : G.A → ℝ) (hν : ∀ a, 0 < ν a) (U : Finset G.V) :
    0 ≤ ((laplacian G ν).submatrix (fun i : U => i.1) (fun i : U => i.1)).det :=
  lem12 G ν hν U
