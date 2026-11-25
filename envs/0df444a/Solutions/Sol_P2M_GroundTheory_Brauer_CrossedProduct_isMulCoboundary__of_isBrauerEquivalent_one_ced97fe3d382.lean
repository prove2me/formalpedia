-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_isBrauerEquivalent_one_ced97fe3d382
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:34.40446+00:00
-- url     : https://prove2.me/submissions/66ef91dc-62f6-43f5-9dfd-b0ad6ba88ffb

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_of_isBrauerEquivalent
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_isBrauerEquivalent_one_one
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_nonempty_algEquiv_of_isBrauerEquivalent

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
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (oneCSA K)) : IsMulCoboundary₂ f := by
  obtain ⟨e⟩ := nonempty_algEquiv_of_isBrauerEquivalent hf isMulCocycle₂_one
    (h.trans (isBrauerEquivalent_one_one (L := L)).symm)
  have h' := isMulCoboundary₂_div_of_algEquiv hf isMulCocycle₂_one e
  rwa [div_one] at h'
end GroundTheory.Brauer.CrossedProduct
