-- Prove2me | solution 1 for ReciprocityTheory.Cheb.preZ_embZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:55.819046+00:00
-- url     : https://prove2.me/submissions/f9a1a725-fe9b-4de6-9a5d-14fd90d7acab

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
theorem _root_.solution (α : 𝓞 E) : preZ (embZ α) = α :=
  Function.leftInverse_invFun embZ_injective α
end ReciprocityTheory.Cheb
