-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_mk_eq_one_549104159c63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:51.05287+00:00
-- url     : https://prove2.me/submissions/64690761-cb8f-4032-a548-fb08b59903d9

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_isBrauerEquivalent_one_ced97fe3d382
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
theorem _root_.solution (hf : IsMulCocycle₂ f)
    (h : (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) = 1) : IsMulCoboundary₂ f :=
  isMulCoboundary₂_of_isBrauerEquivalent_one hf (Quotient.exact (h.trans BrauerGroup.one_def))
end GroundTheory.Brauer.CrossedProduct
