-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.Cyclic.starTranspose_cyclicBoundaryMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:22.724857+00:00
-- url     : https://prove2.me/submissions/61352cda-eee2-411f-98c9-2585371a7e1d

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_groupConj_cyclicBoundaryElement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.Cyclic
theorem _root_.solution
    {G : Type u} [Group G] (x : G) :
    LiftedProduct.starTranspose (cyclicBoundaryMatrix x) =
      cyclicBoundaryMatrix x⁻¹ := by
  funext r c
  cases r
  cases c
  exact groupConj_cyclicBoundaryElement x
end QEC.Coding.BalancedProduct.Cyclic
