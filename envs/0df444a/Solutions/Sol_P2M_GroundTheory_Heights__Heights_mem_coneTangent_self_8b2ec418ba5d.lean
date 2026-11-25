-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_coneTangent_self_8b2ec418ba5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:12.36472+00:00
-- url     : https://prove2.me/submissions/3eaf786f-c5da-4b62-8e68-f38503e3c288

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage

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
theorem _root_.solution {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    y ∈ coneTangent h J y := by
  intro q hq
  have hd : ∀ d, eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) = 0 := by
    intro d
    rw [(homogeneousComponent_isHomogeneous d q).sum_X_mul_pderiv, map_nsmul,
      hy _ (hJ.isHomog q hq d), smul_zero]
  calc ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf y j
      = eval (h.pointOf y) (∑ j, X j * pderiv j q) := by simp [map_sum, mul_comm]
    _ = ∑ d ∈ Finset.range (q.totalDegree + 1),
          eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) := by
        conv_lhs => rw [← sum_homogeneousComponent q]
        simp only [map_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun d _ => hd d
end GroundTheory.Heights₂.Heights
