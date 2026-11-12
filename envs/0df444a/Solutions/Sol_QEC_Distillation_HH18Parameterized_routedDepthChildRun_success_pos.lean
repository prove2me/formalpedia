-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthChildRun_success_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:55:56.483454+00:00
-- url     : https://prove2.me/submissions/ff14579d-b7c4-4d0b-8aaf-35e5481ef0a0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildRun_eq_resourceDecodedRun
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_pos


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
theorem _root_.solution {w r m depth : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    {epsilon : HH18NoisyInput.DiagonalErrorRate}
    {path : routedDepthOutputSlots m w depth}
    {rate : HH18NoisyInput.DiagonalErrorRate}
    (state : RoutedDepthState h hdegree epsilon depth path rate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    0 < (routedDepthChildRun h hdegree state port hhalf).successProbability := by
  rw [routedDepthChildRun_eq_resourceDecodedRun]
  exact endpointWeight_accepted_pos h hdegree
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf)
end QEC.Distillation.HH18Parameterized
