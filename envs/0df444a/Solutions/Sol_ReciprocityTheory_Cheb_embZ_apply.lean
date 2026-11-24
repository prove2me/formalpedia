-- Prove2me | solution 1 for ReciprocityTheory.Cheb.embZ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:48.359361+00:00
-- url     : https://prove2.me/submissions/146e9b6b-3790-4a24-99a7-b5369baaa11f

import Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf

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
theorem _root_.solution (α : 𝓞 E) : embZ α = mixedEmbedding E (α : E) := rfl
end ReciprocityTheory.Cheb
