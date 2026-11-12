-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_eq_scale_mul_errorEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:50:16.324203+00:00
-- url     : https://prove2.me/submissions/94df0c12-f582-4e81-9cd8-ee8746b4e838

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_closed_form


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
    routedDepthScheduleTargetError w r m epsilon depth =
      routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon depth := by
  unfold routedDepthScheduleTargetError
  exact (routedDepthErrorEnvelope_closed_form h epsilon depth).symm
end QEC.Distillation.HH18Parameterized
