-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_succ_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:20:15.168206+00:00
-- url     : https://prove2.me/submissions/f88e7650-b34d-4c64-97a6-04f3900c87f3

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
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
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    decodedRetryPoolStageAggregateShortageBudget w r m epsilon (stage + 1) <=
      decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage / 2 := by
  have hkpos : 0 < (logicalOutputCount m w : Real) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hcoefficient :
      0 <= (logicalOutputCount m w : Real) ^ (stage + 1) *
        decodedRetryPoolDyadicDenominator (stage + 1) *
        physicalInputCount m w := by positivity
  have henv :=
    decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
      h epsilon hpool stage
  have hdyadic :
      (decodedRetryPoolDyadicDenominator (stage + 1) : Real) =
        2 * decodedRetryPoolDyadicDenominator stage := by
    change ((2 ^ (stage + 4) : Nat) : Real) = 2 * ((2 ^ (stage + 3) : Nat) : Real)
    rw [show stage + 4 = (stage + 3) + 1 by omega, pow_succ]
    push_cast
    ring
  unfold decodedRetryPoolStageAggregateShortageBudget
  calc
    (logicalOutputCount m w : Real) ^ (stage + 1) *
          decodedRetryPoolDyadicDenominator (stage + 1) *
          physicalInputCount m w *
          routedDepthErrorEnvelope w r m epsilon (stage + 1) <=
        ((logicalOutputCount m w : Real) ^ (stage + 1) *
          decodedRetryPoolDyadicDenominator (stage + 1) *
          physicalInputCount m w) *
          (routedDepthErrorEnvelope w r m epsilon stage /
            (4 * (logicalOutputCount m w : Real))) :=
      mul_le_mul_of_nonneg_left henv hcoefficient
    _ = ((logicalOutputCount m w : Real) ^ stage *
          decodedRetryPoolDyadicDenominator stage *
          physicalInputCount m w *
          routedDepthErrorEnvelope w r m epsilon stage) / 2 := by
      rw [pow_succ, hdyadic]
      field_simp [ne_of_gt hkpos]
      ring
end QEC.Distillation.HH18Parameterized
