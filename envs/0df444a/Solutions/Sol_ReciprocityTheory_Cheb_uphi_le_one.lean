-- Prove2me | solution 1 for ReciprocityTheory.Cheb.uphi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:41.357528+00:00
-- url     : https://prove2.me/submissions/90046b4e-e034-4a34-85b1-31ebeae031c2

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Theorems.Thm_ReciprocityTheory_Cheb_Tent_le_one__507852


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (x : mixedSpace E) : uphi x ≤ 1 := by
  unfold uphi
  split_ifs
  · exact zero_le_one
  · exact Tent_le_one _
end ReciprocityTheory.Cheb
