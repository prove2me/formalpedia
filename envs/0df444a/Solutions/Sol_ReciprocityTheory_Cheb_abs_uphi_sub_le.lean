-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_uphi_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:57.862153+00:00
-- url     : https://prove2.me/submissions/fb61c1f8-4f12-4db6-b426-2cf122def5d8

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_abs_Tent_sub_Tent_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {x y : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0)
    (hy : mixedEmbedding.norm y ≠ 0) : |uphi x - uphi y| ≤ ∑ i, |ucoord x i - ucoord y i| := by
  unfold uphi
  rw [if_neg hx, if_neg hy]
  exact abs_Tent_sub_Tent_le _ _
end ReciprocityTheory.Cheb
