-- Prove2me | solution 1 for PI.SwSandwichOfWork.logG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:36.164949+00:00
-- url     : https://prove2.me/submissions/ffc30179-50b5-4e8f-874d-ab0a8cc99000

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Theorems.Thm_PI_SwSandwichOfWork_hpk_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution : LogG := by
  intro k r
  have hE : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r)
      ((ContinuousLinearEquiv.refl ℝ (Mat k r) : Mat k r →L[ℝ] Mat k r)) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero
  obtain ⟨ε, hε, hleft⟩ := Metric.eventually_nhds_iff.1 hE.eventually_left_inverse
  set H := Hpk k r
  have hHH : H * H = 1 := hpk_sq
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hHH)
  have hHi : H⁻¹ = H := Matrix.inv_eq_right_inv hHH
  set C := ‖H‖ * ‖H‖ + 1
  have hC : 0 < C := by positivity
  refine ⟨min ε (ε / C), lt_min hε (div_pos hε hC), fun L hL hG => ?_⟩
  have hLε : ‖L‖ < ε := lt_of_lt_of_le hL (min_le_left _ _)
  have hLC : ‖L‖ < ε / C := lt_of_lt_of_le hL (min_le_right _ _)
  have hadj : ‖adjH L‖ < ε := by
    have h1 : ‖adjH L‖ ≤ ‖H‖ * ‖H‖ * ‖L‖ := by
      unfold adjH
      calc ‖H * Lᴴ * H‖ ≤ ‖H * Lᴴ‖ * ‖H‖ := norm_mul_le _ _
        _ ≤ ‖H‖ * ‖Lᴴ‖ * ‖H‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖H‖ * ‖H‖ * ‖L‖ := by rw [Matrix.frobenius_norm_conjTranspose]; ring
    have h2 : ‖H‖ * ‖H‖ * ‖L‖ < ε := by
      calc ‖H‖ * ‖H‖ * ‖L‖ ≤ C * ‖L‖ := by gcongr; simp [C]
        _ < C * (ε / C) := by gcongr
        _ = ε := by field_simp
    linarith
  have hexp : NormedSpace.exp (adjH L) = NormedSpace.exp (-L) := by
    have hG' : (NormedSpace.exp L)ᴴ * H * NormedSpace.exp L = H := hG
    have h1 : NormedSpace.exp (adjH L) = H * (NormedSpace.exp L)ᴴ * H := by
      have := Matrix.exp_conj H Lᴴ hHu
      rw [hHi, Matrix.exp_conjTranspose] at this
      exact this
    have h2 : (H * (NormedSpace.exp L)ᴴ * H) * NormedSpace.exp L = 1 := by
      rw [Matrix.mul_assoc (H * _), show H * (NormedSpace.exp L)ᴴ * (H * NormedSpace.exp L)
        = H * ((NormedSpace.exp L)ᴴ * H * NormedSpace.exp L) by simp only [Matrix.mul_assoc], hG', hHH]
    rw [h1, Matrix.exp_neg, Matrix.inv_eq_left_inv h2]
  have e1 := hleft (y := adjH L) (by simpa using hadj)
  have e2 := hleft (y := -L) (by simpa using hLε)
  rw [hexp] at e1
  show adjH L + L = 0
  rw [← e1, e2, neg_add_cancel]
end PI.SwSandwichOfWork
