-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FsLogSmul_proof_706c8ded022f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:17.736669+00:00
-- url     : https://prove2.me/submissions/85afba7a-f88c-434a-8d44-f1abb96af75a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_smul_947f2ff938a9

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
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace FsLogSmul
theorem _root_.solution : FsLogSmul.Statement := by
  intro n h u y t ht
  unfold fsLog
  have hp : (∑ j, u j * (t • y) j) = t * ∑ j, u j * y j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  rw [hp, h.dualNorm_smul, norm_mul, mul_div_mul_left _ _ ht']
end FsLogSmul
end GroundTheory.Heights₂.Heights
