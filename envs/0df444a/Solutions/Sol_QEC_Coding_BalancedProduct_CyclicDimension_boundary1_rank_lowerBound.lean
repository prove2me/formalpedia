-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.CyclicDimension.boundary1_rank_lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:06:56.937618+00:00
-- url     : https://prove2.me/submissions/c3934bf6-13af-4212-a677-e084064f91e6

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_finrank_range_cyclicDifference
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_cyclicDifference_eq_boundary1_comp_secondZeroExtension

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
    Fintype.card aRow * (q - 1) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (LiftedProduct.boundary1 (Cyclic.data q A))) := by
  rw [← finrank_range_cyclicDifference q aRow,
    cyclicDifference_eq_boundary1_comp_secondZeroExtension q A]
  exact Submodule.finrank_mono
    (LinearMap.range_comp_le_range
      (LiftedProduct.secondZeroExtension (Cyclic.data q A))
      (LiftedProduct.boundary1 (Cyclic.data q A)))
end QEC.Coding.BalancedProduct.CyclicDimension
