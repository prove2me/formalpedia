-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_eq_scheduleTargetError_div_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:00:33.762194+00:00
-- url     : https://prove2.me/submissions/18ed4eb1-532d-48ba-98a3-160508c256aa

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope

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
    routedDepthErrorEnvelope w r m epsilon depth =
      routedDepthScheduleTargetError w r m epsilon depth /
        routedDepthIterationScale w r m := by
  rw [routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope h epsilon depth]
  field_simp [ne_of_gt (routedDepthIterationScale_pos w r m)]
end QEC.Distillation.HH18Parameterized
