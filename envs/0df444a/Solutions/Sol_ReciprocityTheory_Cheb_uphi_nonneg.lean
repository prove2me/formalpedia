-- Prove2me | solution 1 for ReciprocityTheory.Cheb.uphi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:54.766259+00:00
-- url     : https://prove2.me/submissions/9f37f078-2be6-42f1-abe8-832b419c73ab

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Theorems.Thm_ReciprocityTheory_Cheb_Tent_nonneg__b8ca4a


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
theorem _root_.solution (x : mixedSpace E) : 0 ≤ uphi x := by
  unfold uphi
  split_ifs
  · exact le_rfl
  · exact Tent_nonneg _
end ReciprocityTheory.Cheb
