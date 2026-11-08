-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.mem_localParityCheck_kernel_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:24:04.895637+00:00
-- url     : https://prove2.me/submissions/53c311f5-8d14-470b-9422-b27cb96bea37

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner

set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
namespace QEC.Coding.BalancedProduct.LPSTanner
theorem _root_.solution
    (w : Word (ZMod 2) LocalCoordinate) :
    w ∈ (parityCheckKernelCode localParityCheck).carrier ↔
      w ∈ localCode.carrier := by
  rw [mem_parityCheckKernelCode]
  change localParityCheck w = 0 ↔
    w ∈ (systematicCode localMatrix).carrier
  rw [mem_systematicCode]
  constructor
  · intro hw
    refine ⟨fun i => w (Sum.inl i), ?_⟩
    funext x
    cases x with
    | inl i => rfl
    | inr j =>
        have hj := congrFun hw j
        change w (Sum.inr j) -
          Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j = 0 at hj
        exact (sub_eq_zero.mp hj).symm
  · rintro ⟨m, rfl⟩
    exact localParityCheck_systematicEncode m
end QEC.Coding.BalancedProduct.LPSTanner
