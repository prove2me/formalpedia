-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.signedSwapWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:19.107069+00:00
-- url     : https://prove2.me/submissions/fbd92e44-7f53-4178-9137-f41b619ffde1

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Theorems.Thm_QEC_Coding_LiftedProduct_boundary1_dualData_signedSwapWord

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (z : Word F (QubitIndex aRow aCol bRow bCol G))
    (hz : z ∈ (chainComplex D).middleCocycleCode.carrier) :
    signedSwapWord z ∈
      (chainComplex (dualData D)).middleCycleCode.carrier := by
  rw [(chainComplex (dualData D)).mem_middleCycleCode_iff]
  rw [chainComplex_boundary1, boundary1_dualData_signedSwapWord]
  exact ((chainComplex D).mem_middleCocycleCode_iff z).1 hz
end QEC.Coding.LiftedProduct
