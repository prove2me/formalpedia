-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneFibreAverage_of_lt_6291d9b63762
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:54.144965+00:00
-- url     : https://prove2.me/submissions/011e9c52-cd85-4be1-adf3-aba88c2e51af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      1 * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 * n < 2 * m)
  rw [Real.hausdorffMeasure_of_finrank_lt hlt, Measure.coe_zero, Pi.zero_apply, mul_zero]
  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) = 0 := by
    intro π
    rw [lintegral_congr_ae (g := fun _ => 0) (ae_restrict_of_ae (by
        filter_upwards [ae_fibreCount_eq_zero hnm h J π] with w hw
        simp [hw])), lintegral_zero]
  simp [hin]
end GroundTheory.Heights₂.Heights
