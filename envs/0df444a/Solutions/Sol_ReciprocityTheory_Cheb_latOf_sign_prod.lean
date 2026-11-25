-- Prove2me | solution 1 for ReciprocityTheory.Cheb.latOf_sign_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:05.015443+00:00
-- url     : https://prove2.me/submissions/b6dafd46-708a-4a81-bc5a-0f01ab176ca8

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
open NumberField.InfinitePlace
namespace ReciprocityTheory.Cheb
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    SignType.sign (∏ i ∈ s, f i) = ∏ i ∈ s, SignType.sign (f i) :=
  map_prod (signHom : ℝ →*₀ SignType) f s
end ReciprocityTheory.Cheb
