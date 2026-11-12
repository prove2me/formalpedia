-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_eq_resourceDecodedRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:41:06.853955+00:00
-- url     : https://prove2.me/submissions/2f4813dc-fdeb-4bd0-9ee0-38d3265c14af

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
      resourceDecodedRun h hdegree (noisyResources m w
        (routedDepthPathRate h hdegree epsilon hsmall depth path)) :=
  rfl
end QEC.Distillation.HH18Parameterized
