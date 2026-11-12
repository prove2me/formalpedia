-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_eq_distancePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:59:56.264088+00:00
-- url     : https://prove2.me/submissions/ce0d000e-20e4-49ba-a34a-38eb9bfc2011

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_codeDistance_eq_binomialTail


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
theorem _root_.solution (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth =
      (routedDepthIterationScale w r m * epsilon.1) ^
        (binomialTail (r + 1) w ^ depth) := by
  unfold routedDepthScheduleTargetError
  rw [codeDistance_eq_binomialTail]
end QEC.Distillation.HH18Parameterized
