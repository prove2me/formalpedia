-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_sum_sq_pos_4baf91b15745
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:17:06.500078+00:00
-- url     : https://prove2.me/submissions/7d7d2b78-1427-4699-8c27-09741d41824b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanLinearBall

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanLinearBall
namespace GroundTheory.Heights₂.Heights.SphereMeanLinearBall
theorem _root_.solution {n : ℕ} {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < ∑ j, ‖y j‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hy ?_
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖y j‖).mp h.symm
  funext j
  simpa using h0 j (Finset.mem_univ j)
end GroundTheory.Heights₂.Heights.SphereMeanLinearBall
