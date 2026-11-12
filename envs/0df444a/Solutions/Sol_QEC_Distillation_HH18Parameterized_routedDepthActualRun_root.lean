-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthActualRun_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:53:52.189566+00:00
-- url     : https://prove2.me/submissions/b236e2cf-e96f-47b6-a30a-acaffe20b108

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    routedDepthActualRun h hdegree (RoutedDepthState.root (h := h)
      (hdegree := hdegree) (epsilon := epsilon)) =
      resourceDecodedRun h hdegree (noisyResources m w epsilon) :=
  rfl
end QEC.Distillation.HH18Parameterized
