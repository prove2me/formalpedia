-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_algEquiv_matrix_a8775355bc14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:12.62614+00:00
-- url     : https://prove2.me/submissions/189bebdf-f511-4cf7-a058-6c7ee01ec6b1

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq


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
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
variable [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hf : IsMulCocycle₂ f) (e : CrossedProduct hf ≃ₐ[K] Matrix ι ι K) : IsMulCoboundary₂ f := by
  have hcard : Fintype.card ι = Module.finrank K L := by
    have h1 := e.toLinearEquiv.finrank_eq
    rw [finrank_eq_sq, Module.finrank_matrix, Module.finrank_self, mul_one, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have h := isMulCoboundary₂_div_of_algEquiv hf isMulCocycle₂_one
    (e.trans ((Matrix.reindexAlgEquiv K K (Fintype.equivFinOfCardEq hcard)).trans
      (matrixEquiv isMulCocycle₂_one).symm))
  rwa [div_one] at h
end GroundTheory.Brauer.CrossedProduct
