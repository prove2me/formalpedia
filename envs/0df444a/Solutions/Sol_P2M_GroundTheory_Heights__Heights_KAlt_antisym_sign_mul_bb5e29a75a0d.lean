-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_antisym_sign_mul_bb5e29a75a0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:02.208154+00:00
-- url     : https://prove2.me/submissions/b5d60956-3f2e-4dc2-bedc-33c3c5873979

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_antisym_eq_sum_314cba1d0338

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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (a : Equiv.Perm ι) (p : MvPolynomial ι ℚ) :
    antisym (sgnP a * p) = sgnP a * antisym p := by
  simp only [antisym_eq_sum, map_mul, sgnP, map_intCast, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  ring
end GroundTheory.Heights₂.Heights.KAlt
