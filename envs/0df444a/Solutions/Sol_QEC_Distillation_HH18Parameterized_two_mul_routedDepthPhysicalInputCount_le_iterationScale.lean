-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.two_mul_routedDepthPhysicalInputCount_le_iterationScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:40:36.975207+00:00
-- url     : https://prove2.me/submissions/13e363ed-5337-4b7e-98bf-4852d71f9889

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope

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
theorem _root_.solution (w r m : Nat) :
    2 * (physicalInputCount m w : ℝ) ≤ routedDepthIterationScale w r m := by
  have hcount : 0 ≤ (physicalInputCount m w : ℝ) := Nat.cast_nonneg _
  unfold routedDepthIterationScale
  nlinarith [routedDepthRawErrorCoefficient_nonneg w r m, hcount]
end QEC.Distillation.HH18Parameterized
