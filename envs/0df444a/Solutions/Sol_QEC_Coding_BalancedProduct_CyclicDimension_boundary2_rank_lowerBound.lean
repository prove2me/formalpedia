-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.CyclicDimension.boundary2_rank_lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:06:57.700556+00:00
-- url     : https://prove2.me/submissions/aff12b33-8212-442c-9ced-98020b0ed78b

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_finrank_range_cyclicDifference
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_cyclicDifference_eq_firstRestriction_comp_boundary2

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u
namespace QEC.Coding.BalancedProduct.CyclicDimension
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol * (q - 1) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (LiftedProduct.boundary2 (Cyclic.data q A))) := by
  rw [← finrank_range_cyclicDifference q aCol,
    cyclicDifference_eq_firstRestriction_comp_boundary2 q A]
  exact Module.finrank_le_finrank_of_rank_le_rank
    (LinearMap.lift_rank_comp_le_right
      (LiftedProduct.boundary2 (Cyclic.data q A))
      (LiftedProduct.firstRestriction (Cyclic.data q A)))
    (Module.rank_lt_aleph0 (ZMod 2)
      (LinearMap.range (LiftedProduct.boundary2 (Cyclic.data q A))))
end QEC.Coding.BalancedProduct.CyclicDimension
