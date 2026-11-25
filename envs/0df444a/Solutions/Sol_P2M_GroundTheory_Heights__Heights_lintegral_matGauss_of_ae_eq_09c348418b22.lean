-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_lintegral_matGauss_of_ae_eq_09c348418b22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:55.789464+00:00
-- url     : https://prove2.me/submissions/1f2a58fc-b4b0-43ac-a31d-5e4b91755ba9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre

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
theorem _root_.solution {m n : ℕ} (c : ℕ)
    (N : (Fin m → Fin n → ℂ) → EuclideanSpace ℂ (Fin m) → ℕ∞)
    (hN : ∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), N π w = c) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (N π w : ℝ≥0∞) =
      (c : ℝ≥0∞) * ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) := by
  rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top c)]
  refine lintegral_congr_ae ?_
  filter_upwards [hN] with π hπ
  have hin : ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (N π w : ℝ≥0∞) =
      ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (c : ℝ≥0∞) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hπ] with w hw
    rw [hw]
    simp
  rw [hin, setLIntegral_const]
  ring
end GroundTheory.Heights₂.Heights
