-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.finrank_middleHomology_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:57.364978+00:00
-- url     : https://prove2.me/submissions/8aa4f0d1-881c-40a0-ab39-9548a4795477

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_card_sub_card_le_finrank_middleHomology
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_finrank_middleHomology_le_card_add_card


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hOdd : Odd q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol - Fintype.card aRow ≤
        Module.finrank (ZMod 2)
          (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ∧
      Module.finrank (ZMod 2)
          (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ≤
        Fintype.card aCol + Fintype.card aRow :=
  ⟨card_sub_card_le_finrank_middleHomology q hOdd A,
    CyclicDimension.finrank_middleHomology_le_card_add_card q A⟩
end QEC.Coding.ExpanderCodes.PK20
