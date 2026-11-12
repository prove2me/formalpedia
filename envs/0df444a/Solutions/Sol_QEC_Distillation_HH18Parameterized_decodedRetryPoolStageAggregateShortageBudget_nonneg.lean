-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:11:19.015681+00:00
-- url     : https://prove2.me/submissions/b2adfa33-6a48-492d-a62b-efd3cb5487d3

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolErrorEnvelope_nonneg

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
    (w r m : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (stage : Nat) :
    0 <= decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage := by
  unfold decodedRetryPoolStageAggregateShortageBudget
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
    (decodedRetryPoolErrorEnvelope_nonneg w r m epsilon stage)
end QEC.Distillation.HH18Parameterized
