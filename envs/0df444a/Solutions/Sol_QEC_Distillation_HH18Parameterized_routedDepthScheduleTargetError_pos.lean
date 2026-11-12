-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:00:51.617222+00:00
-- url     : https://prove2.me/submissions/e8b46e7f-de89-4e91-b370-a69125466c79

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (depth : Nat) :
    0 < routedDepthScheduleTargetError w r m epsilon depth := by
  unfold routedDepthScheduleTargetError
  exact pow_pos (mul_pos (routedDepthIterationScale_pos w r m) hepsilon) _
end QEC.Distillation.HH18Parameterized
