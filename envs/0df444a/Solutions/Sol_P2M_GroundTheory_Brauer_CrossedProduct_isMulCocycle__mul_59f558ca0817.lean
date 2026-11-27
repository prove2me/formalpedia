-- Prove2me | solution 1 for P2M_GroundTheory_Brauer_CrossedProduct_isMulCocycle__mul_59f558ca0817
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:16.994646+00:00
-- url     : https://prove2.me/submissions/5d94ab22-da89-4dc4-9a2b-16827fbbff09

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor

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
open groupCohomology TensorProduct
universe u
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [DecidableEq (L ≃ₐ[K] L)]
variable {f g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
omit [FiniteDimensional K L] [DecidableEq (L ≃ₐ[K] L)]
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) : IsMulCocycle₂ (f * g) :=
  (mulCocycles₂ (L ≃ₐ[K] L) Lˣ).mul_mem hf hg
end GroundTheory.Brauer.CrossedProduct
