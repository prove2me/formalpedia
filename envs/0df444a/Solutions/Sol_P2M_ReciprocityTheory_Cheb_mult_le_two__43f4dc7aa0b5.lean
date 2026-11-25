-- Prove2me | solution 1 for P2M_ReciprocityTheory_Cheb_mult_le_two__43f4dc7aa0b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:09.222799+00:00
-- url     : https://prove2.me/submissions/28f4e8fa-d27f-436d-9eec-a80af317e0e6

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

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
theorem _root_.solution (w : InfinitePlace E) : (mult w : ℝ) ≤ 2 := by
  unfold mult; split_ifs <;> norm_num
end ReciprocityTheory.Cheb
