-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:40.761138+00:00
-- url     : https://prove2.me/submissions/9bdb52a5-b31f-4923-ae81-18e678a626ab

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_boundary1_dualData_swapWord

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
theorem _root_.solution
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G))
    (hz : z ∈ (LiftedProduct.chainComplex D).middleCocycleCode.carrier) :
    swapWord z ∈
      (LiftedProduct.chainComplex (dualData D)).middleCycleCode.carrier := by
  rw [(LiftedProduct.chainComplex (dualData D)).mem_middleCycleCode_iff]
  rw [LiftedProduct.chainComplex_boundary1, boundary1_dualData_swapWord]
  exact ((LiftedProduct.chainComplex D).mem_middleCocycleCode_iff z).1 hz
end QEC.Coding.BalancedProduct.LiftedProductDuality
