-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.transposeTannerWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:50:27.343656+00:00
-- url     : https://prove2.me/submissions/df3ad104-b5a5-48cd-9c5b-7271c407bd42

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_transposeTannerWord_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hz : z ∈ (chainComplex label h h').middleCocycleCode.carrier) :
    transposeTannerWord inverseDirection z ∈
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).middleCycleCode.carrier := by
  rw [(chainComplex targetLabel (reindexColumns inverseDirection h')
    (reindexColumns inverseDirection h)).mem_middleCycleCode_iff]
  funext c0
  obtain ⟨c2, rfl⟩ := (transposeEdgeEquiv inverseDirection).surjective c0
  rw [chainComplex, LiftedProduct.chainComplex_boundary1,
    boundary1_transposeTannerWord_apply
      label targetLabel inverseDirection hInverse h h']
  exact congrFun
    (((chainComplex label h h').mem_middleCocycleCode_iff z).1 hz) c2
end QEC.Coding.TannerLiftedProduct
