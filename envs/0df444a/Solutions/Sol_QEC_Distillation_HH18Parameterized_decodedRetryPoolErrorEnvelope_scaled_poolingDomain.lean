-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_scaled_poolingDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:10:57.678874+00:00
-- url     : https://prove2.me/submissions/f6ee8b55-bf38-4b98-a71a-7da8e7e0b4a4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_closed_form
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
    routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon stage <=
      1 / (64 * (logicalOutputCount m w : Real)) := by
  rw [routedDepthErrorEnvelope_closed_form h epsilon]
  have hkpos : 0 < (logicalOutputCount m w : Real) := by
    exact_mod_cast routedDepthLogicalOutputCount_pos m w
  have hden : 0 < (64 : Real) * logicalOutputCount m w := mul_pos (by norm_num) hkpos
  have hthresholdNonneg :
      0 <= 1 / ((64 : Real) * logicalOutputCount m w) := (one_div_pos.mpr hden).le
  have hthresholdLeOne :
      1 / ((64 : Real) * logicalOutputCount m w) <= 1 := by
    apply (div_le_iff₀ hden).2
    have hk : (1 : Real) <= logicalOutputCount m w := by
      exact_mod_cast Nat.succ_le_iff.mpr (routedDepthLogicalOutputCount_pos m w)
    nlinarith
  have hbase : 0 <= routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hdistance : 2 <= codeDistance r w := codeDistance_two_le h
  have hpower : 1 <= codeDistance r w ^ stage :=
    one_le_pow₀ (by omega : 1 <= codeDistance r w)
  calc
    (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ stage) <=
        (1 / ((64 : Real) * logicalOutputCount m w)) ^
          (codeDistance r w ^ stage) :=
      pow_le_pow_left₀ hbase hpool _
    _ <= (1 / ((64 : Real) * logicalOutputCount m w)) ^ 1 :=
      pow_le_pow_of_le_one hthresholdNonneg hthresholdLeOne hpower
    _ = 1 / (64 * (logicalOutputCount m w : Real)) := by ring
end QEC.Distillation.HH18Parameterized
