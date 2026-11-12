-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_eq_routedDepthActualRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:57:33.137198+00:00
-- url     : https://prove2.me/submissions/f22f3cbb-002e-4b34-af15-16a23d594cf4

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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathActualRun h hdegree epsilon hsmall depth path =
      routedDepthActualRun h hdegree
        (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).state :=
  rfl
end QEC.Distillation.HH18Parameterized
