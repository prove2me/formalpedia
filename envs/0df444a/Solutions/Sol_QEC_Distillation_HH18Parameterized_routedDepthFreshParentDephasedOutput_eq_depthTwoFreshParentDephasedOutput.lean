-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthFreshParentDephasedOutput_eq_depthTwoFreshParentDephasedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:54:09.437201+00:00
-- url     : https://prove2.me/submissions/771174f3-d9e9-417a-826d-77521f32ce7e

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
theorem _root_.solution
    {w r m depth : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (source : depthTwoParentOutputSlots m w) :
    routedDepthFreshParentDephasedOutput h hdegree state source =
      depthTwoFreshParentDephasedOutput h hdegree rate source :=
  rfl
end QEC.Distillation.HH18Parameterized
