-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeFsLog_sum_mul_pointOf_e015eaf40c49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:15.578519+00:00
-- url     : https://prove2.me/submissions/482a2cd6-6407-4174-9901-0bed6ec8e909

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable

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
open MvPolynomial MeasureTheory Set Matrix Filter
noncomputable section
open GroundTheory.Heights₂.Heights.ConeFsLog
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeFsLog
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf y j = ∑ i, (h.mat *ᵥ u) i * y i := by
  simp only [HermNorm.pointOf, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GroundTheory.Heights₂.Heights.ConeFsLog
