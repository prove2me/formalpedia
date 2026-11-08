-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.localTranspose_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:30:16.973909+00:00
-- url     : https://prove2.me/submissions/5408eb40-2682-43d5-91a3-c4b31663f639

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_wordLinearMapTranspose_localParityCheck
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localMatrix_dual_weight_lower_bound


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype
namespace QEC.Coding.BalancedProduct.LPSTanner
theorem _root_.solution
    (y : Word (ZMod 2) (Fin 200)) (hy : y ≠ 0) :
    41 ≤ HammingWeight (wordLinearMapTranspose localParityCheck y) := by
  rw [wordLinearMapTranspose_localParityCheck]
  exact localMatrix_dual_weight_lower_bound y hy
end QEC.Coding.BalancedProduct.LPSTanner
