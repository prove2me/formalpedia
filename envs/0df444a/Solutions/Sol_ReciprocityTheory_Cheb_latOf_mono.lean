-- Prove2me | solution 1 for ReciprocityTheory.Cheb.latOf_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:59.766094+00:00
-- url     : https://prove2.me/submissions/aa6b0281-d856-4d9b-b36a-caf50e0f10d5

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
theorem _root_.solution {I J : Ideal (𝓞 E)} (h : I ≤ J) : latOf I ≤ latOf J :=
  Submodule.map_mono (fun _ hx => h hx)
end ReciprocityTheory.Cheb
