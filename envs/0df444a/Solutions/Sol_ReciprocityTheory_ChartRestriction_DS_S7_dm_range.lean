-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:52.240306+00:00
-- url     : https://prove2.me/submissions/bcd06494-5db1-425e-ada7-81f99ea0a58c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (J : Finset (Fin n)) :
    |∑ j ∈ J, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) := by
  unfold hs
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, (((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ)) : ℂ) = (M * Mᴴ).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    first
      | (rw [Complex.star_def, Complex.mul_conj'])
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
      | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htr : (Y * Yᴴ).trace = (((∑ j, y j ^ 2 : ℝ)) : ℂ) := by
    rw [hY]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.conj_ofReal, sq]
  have hsum : ∑ i, ∑ j, ‖Y i j‖ ^ 2 = ∑ j, y j ^ 2 := by
    have h := key Y
    rw [htr] at h
    exact_mod_cast h
  have hT : ∑ j ∈ J, y j = ∑ j ∈ J.filter (fun j => y j ≠ 0), y j :=
    (Finset.sum_filter_ne_zero _).symm
  have hcard : (J.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ J))).trans
      (dm_card_le hU hY hYp)
  have hcs : (∑ j ∈ J.filter (fun j => y j ≠ 0), y j) ^ 2 ≤
      ((J.filter fun j => y j ≠ 0).card : ℝ) * ∑ j, y j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (J.filter fun j => y j ≠ 0) (fun _ => (1 : ℝ)) y
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
  rw [hsum, ← Real.sqrt_mul (by positivity), hT]
  apply Real.abs_le_sqrt
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _))
  exact_mod_cast hcard
end ReciprocityTheory.ChartRestriction.DS.S7
