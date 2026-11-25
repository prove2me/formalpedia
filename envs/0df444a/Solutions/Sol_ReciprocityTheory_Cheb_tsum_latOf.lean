-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tsum_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:53.569603+00:00
-- url     : https://prove2.me/submissions/56d6a3b6-26ce-475c-ae1c-2fda02ec62dc

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
theorem _root_.solution (I : Ideal (𝓞 E)) (g : mixedSpace E → ℂ) :
    ∑' x : latOf I, g x = ∑' α : I, g (embZ (α : 𝓞 E)) :=
  ((latEquiv I).tsum_eq (fun x : latOf I => g x)).symm
end ReciprocityTheory.Cheb
