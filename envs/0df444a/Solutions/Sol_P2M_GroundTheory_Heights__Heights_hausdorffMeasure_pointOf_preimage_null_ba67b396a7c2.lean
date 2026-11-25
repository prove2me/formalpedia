-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hausdorffMeasure_pointOf_preimage_null_ba67b396a7c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:27.693477+00:00
-- url     : https://prove2.me/submissions/5cbcdeb6-a5be-427f-8c01-e71d4564d8cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeKrullDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentDim

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by
  let E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let F := LinearMap.toContinuousLinearMap E.symm.toLinearMap
  refine measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_
  · simp [F]
  · exact le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))
end GroundTheory.Heights₂.Heights
