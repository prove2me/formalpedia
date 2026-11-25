-- Prove2me | solution 1 for ReciprocityTheory.Cheb.uphi_embZ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:46:10.543956+00:00
-- url     : https://prove2.me/submissions/d4901696-c887-4823-823b-f9730bf0d926

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Theorems.Thm_ReciprocityTheory_Cheb_norm_embZ
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_of_norm_eq_zero


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
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution : uphi (embZ (0 : 𝓞 E)) = 0 := by
  apply uphi_of_norm_eq_zero
  rw [norm_embZ]; simp
end ReciprocityTheory.Cheb
