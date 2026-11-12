-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolRequired_le_dyadicAttempts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:06:44.601717+00:00
-- url     : https://prove2.me/submissions/5ea1ec42-a806-46c0-a997-051a56ebd1f8

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_FirstMoment
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
section
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
private theorem decodedRetryPoolDyadicDenominator_ge_eight (stage : Nat) :
    8 ≤ decodedRetryPoolDyadicDenominator stage := by
  unfold decodedRetryPoolDyadicDenominator
  calc
    8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (stage + 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
private theorem decodedRetryPoolDyadicDenominator_sub_one_pos (stage : Nat) :
    0 < decodedRetryPoolDyadicDenominator stage - 1 := by
  have hden := decodedRetryPoolDyadicDenominator_ge_eight stage
  omega
end HH18Parameterized
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedRetryPoolDyadicSlackClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (stage required : Nat) :
    required ≤ decodedRetryPoolDyadicAttempts stage required := by
  unfold decodedRetryPoolDyadicAttempts decodedRetryPoolCeilDiv
  apply (Nat.le_div_iff_mul_le
    (decodedRetryPoolDyadicDenominator_sub_one_pos stage)).2
  calc
    required * (decodedRetryPoolDyadicDenominator stage - 1) ≤
        required * decodedRetryPoolDyadicDenominator stage :=
      Nat.mul_le_mul_left required (Nat.sub_le _ _)
    _ = decodedRetryPoolDyadicDenominator stage * required := Nat.mul_comm _ _
    _ ≤ decodedRetryPoolDyadicDenominator stage * required +
        (decodedRetryPoolDyadicDenominator stage - 1) - 1 :=
      by
        have hroom : 1 ≤ decodedRetryPoolDyadicDenominator stage - 1 := by
          have hdenominator := decodedRetryPoolDyadicDenominator_ge_eight stage
          omega
        omega
end QEC.Distillation.HH18Parameterized
