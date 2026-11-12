-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPooledAcceptedOutput_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:46:25.196109+00:00
-- url     : https://prove2.me/submissions/0ee97834-4bd9-4d1c-9945-b35c7ac1ef96

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield

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
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthPooledAcceptedOutput h hdegree epsilon hsmall depth : ℝ) =
      ∑ path : routedDepthOutputSlots m w depth,
        (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) := by
  classical
  rw [routedDepthPooledAcceptedOutput, NNReal.coe_sum]
end QEC.Distillation.HH18Parameterized
