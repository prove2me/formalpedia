-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_cyclicLiftedProductData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:37.287758+00:00
-- url     : https://prove2.me/submissions/18e294fe-1b9c-4e27-9aee-c8f45591c3f8

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_starTranspose_cyclicBoundaryMatrix


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
theorem _root_.solution
    {G aRow aCol : Type u} [Group G]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G) :
    dualData (Cyclic.liftedProductData A x) =
      Cyclic.liftedProductData (LiftedProduct.starTranspose A) x⁻¹ := by
  unfold dualData Cyclic.liftedProductData
  rw [Cyclic.starTranspose_cyclicBoundaryMatrix]
end QEC.Coding.BalancedProduct.LiftedProductDuality
