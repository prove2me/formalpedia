-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_le_scheduleTargetError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:51:06.013672+00:00
-- url     : https://prove2.me/submissions/864e66de-8262-4bd3-b79c-869a3cea28e3

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleErrorEnvelope_nonneg

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon depth ≤
      routedDepthScheduleTargetError w r m epsilon depth := by
  rw [routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope h epsilon depth]
  nlinarith [routedDepthIterationScale_one_le w r m,
    routedDepthScheduleErrorEnvelope_nonneg w r m epsilon depth]
end QEC.Distillation.HH18Parameterized
