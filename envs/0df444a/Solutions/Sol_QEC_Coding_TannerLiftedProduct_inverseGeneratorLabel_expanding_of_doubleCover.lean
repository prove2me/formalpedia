-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.inverseGeneratorLabel_expanding_of_doubleCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:31:16.697016+00:00
-- url     : https://prove2.me/submissions/8172e7a1-3f3f-45f7-9901-6eef3db37ce5

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_relabel


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq W]
    [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph (inverseGeneratorLabel label)) radius lambda := by
  rw [rightDoubleCoverGraph_inverseGeneratorLabel_eq_relabel]
  exact hBase.relabel doubleCoverSideSwapEquiv
end QEC.Coding.TannerLiftedProduct
