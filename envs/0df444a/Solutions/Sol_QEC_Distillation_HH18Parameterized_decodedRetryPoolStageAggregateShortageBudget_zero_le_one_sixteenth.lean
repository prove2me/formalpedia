-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_zero_le_one_sixteenth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:11:59.275882+00:00
-- url     : https://prove2.me/submissions/fc060c27-056d-4208-bafe-19244f3d42c8

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthLogicalOutputCount_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_two_mul_routedDepthPhysicalInputCount_le_iterationScale


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
    decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 <= 1 / 16 := by
  have hk : (1 : Real) <= logicalOutputCount m w := by
    exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
  have hkpos : 0 < (logicalOutputCount m w : Real) := lt_of_lt_of_le zero_lt_one hk
  have hden : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hthreshold :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 / 64 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hcountScale := two_mul_routedDepthPhysicalInputCount_le_iterationScale w r m
  have hscaled :
      (2 * (physicalInputCount m w : Real)) * epsilon.1 <=
        routedDepthIterationScale w r m * epsilon.1 :=
    mul_le_mul_of_nonneg_right hcountScale epsilon.property.1
  have hcountEpsilon :
      (physicalInputCount m w : Real) * epsilon.1 <= 1 / 128 := by
    nlinarith [hscaled, hpool.trans hthreshold]
  change (logicalOutputCount m w : Real) ^ 0 *
      decodedRetryPoolDyadicDenominator 0 * physicalInputCount m w * epsilon.1 <= 1 / 16
  norm_num [decodedRetryPoolDyadicDenominator]
  nlinarith
end QEC.Distillation.HH18Parameterized
