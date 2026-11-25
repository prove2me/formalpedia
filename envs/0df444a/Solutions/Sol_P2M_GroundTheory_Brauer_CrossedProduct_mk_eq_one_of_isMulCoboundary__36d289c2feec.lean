-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_mk_eq_one_of_isMulCoboundary__36d289c2feec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:09.663793+00:00
-- url     : https://prove2.me/submissions/8f7cee22-e689-4356-b72f-009fd274f469

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_isBrauerEquivalent_one_one
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_one_def


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
open groupCohomology
universe u v
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1 := by
  rw [BrauerGroup.one_def]
  refine Quotient.sound (IsBrauerEquivalent.trans ?_ (isBrauerEquivalent_one_one (L := L)))
  refine isBrauerEquivalent_of_algEquiv
    (A := csaOf K (CrossedProduct hf)) (B := csaOf K (CrossedProduct (isMulCocycle₂_one (K := K)
      (L := L)))) (equivOfIsMulCoboundary₂ hf isMulCocycle₂_one ?_)
  rw [one_div]
  exact isMulCoboundary₂_inv h
end GroundTheory.Brauer.CrossedProduct
