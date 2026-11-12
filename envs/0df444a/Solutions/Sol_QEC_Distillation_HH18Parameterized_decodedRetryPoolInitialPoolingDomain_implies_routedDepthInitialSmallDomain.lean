-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:00:06.785206+00:00
-- url     : https://prove2.me/submissions/73c36fdb-613d-430f-8972-f9898047cda5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    routedDepthInitialSmallDomain w r m epsilon := by
  have hk : (1 : Real) <= logicalOutputCount m w := by
    exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
  have hkpos : 0 < (logicalOutputCount m w : Real) := lt_of_lt_of_le zero_lt_one hk
  have hden : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hquarter :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 / 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  exact hpool.trans hquarter
end QEC.Distillation.HH18Parameterized
