-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_exists_algEquiv_of_isMulCoboundary__ca4eaaf3483d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:09.062659+00:00
-- url     : https://prove2.me/submissions/7b041a76-1cb5-4bc3-9df6-9c830ba5fea8

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open GroundTheory.Brauer.CrossedProduct
open groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
variable {f' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) :
    ∃ e : CrossedProduct hf ≃ₐ[K] CrossedProduct hf', ∀ a : L, e (incl a) = incl a :=
  ⟨equivOfIsMulCoboundary₂ hf hf' h, equivOfIsMulCoboundary₂_incl hf hf' h⟩
end GroundTheory.Brauer.CrossedProduct
