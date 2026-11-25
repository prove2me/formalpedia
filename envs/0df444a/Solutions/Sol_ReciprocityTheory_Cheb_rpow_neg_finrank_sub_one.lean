-- Prove2me | solution 1 for ReciprocityTheory.Cheb.rpow_neg_finrank_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:44.349408+00:00
-- url     : https://prove2.me/submissions/2e1e94f3-0623-4527-b7ea-09f3afe12142

import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    t ^ (-(n : ℝ) - 1) = (t ^ (n + 1))⁻¹ := by
  rw [show -(n : ℝ) - 1 = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg ht, Real.rpow_natCast]
end ReciprocityTheory.Cheb
