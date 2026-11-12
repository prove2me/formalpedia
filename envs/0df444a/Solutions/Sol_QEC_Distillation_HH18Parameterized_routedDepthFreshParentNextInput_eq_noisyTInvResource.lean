-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthFreshParentNextInput_eq_noisyTInvResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:54:33.272216+00:00
-- url     : https://prove2.me/submissions/52be005c-3d41-419b-94f5-f1a51b8dcaba

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoFreshParentNextInput_eq_noisyTInvResource


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
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthFreshParentNextInput h hdegree state (parent, port) =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf) := by
  change depthTwoFreshParentNextInput h hdegree rate (parent, port) = _
  exact depthTwoFreshParentNextInput_eq_noisyTInvResource h hdegree rate
    (parent, port) hhalf
end QEC.Distillation.HH18Parameterized
