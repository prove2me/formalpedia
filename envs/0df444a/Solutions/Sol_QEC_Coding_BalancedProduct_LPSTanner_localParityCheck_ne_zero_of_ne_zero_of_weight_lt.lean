-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.localParityCheck_ne_zero_of_ne_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:26:09.502671+00:00
-- url     : https://prove2.me/submissions/beafd2d8-07d3-42b1-aa24-bcd5bc974379

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_mem_localParityCheck_kernel_iff
import Theorems.Thm_QEC_Coding_BalancedProduct_GVPlus_localCode_primal_weight_lower_bound


set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype
namespace QEC.Coding.BalancedProduct.LPSTanner
theorem _root_.solution
    (w : Word (ZMod 2) LocalCoordinate)
    (hw0 : w ≠ 0)
    (hw : HammingWeight w < 41) :
    localParityCheck w ≠ 0 := by
  intro hcheck
  have hkernel :
      w ∈ (parityCheckKernelCode localParityCheck).carrier :=
    (mem_parityCheckKernelCode localParityCheck w).2 hcheck
  have hcode : w ∈ localCode.carrier :=
    (mem_localParityCheck_kernel_iff w).1 hkernel
  have hlower := localCode_primal_weight_lower_bound w hcode hw0
  omega
end QEC.Coding.BalancedProduct.LPSTanner
