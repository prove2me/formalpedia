-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeRadialIntegral_hypotheses_inhabited_907333c931e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:21.640007+00:00
-- url     : https://prove2.me/submissions/f3dd06bf-f631-482c-bb17-17767a320680

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce


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
variable {m n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeRadialIntegral
theorem _root_.solution :
    0 < 1 ∧
      (∀ y ∈ {y : EuclideanSpace ℂ (Fin (1 + 1)) | ∀ j : Fin (1 + 1), 1 ≤ (j : ℕ) → y j = 0},
        ∀ t : ℝ, 0 < t → t • y ∈ {y : EuclideanSpace ℂ (Fin (1 + 1)) | ∀ j : Fin (1 + 1), 1 ≤ (j : ℕ) → y j = 0}) ∧
      Measure.hausdorffMeasure ((2 * 1 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin (1 + 1)) | ‖y‖ < 1 ∧ ∀ j : Fin (1 + 1), 1 ≤ (j : ℕ) → y j = 0} < ⊤ ∧
      Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r ^ 2))) := by
  refine ⟨one_pos, ?_, (coordBall_mass (by norm_num : 1 ≤ 1 + 1)).2, by fun_prop⟩
  intro y hy t _ j hj
  simp [hy j hj]
end ConeRadialIntegral
end GroundTheory.Heights₂.Heights
