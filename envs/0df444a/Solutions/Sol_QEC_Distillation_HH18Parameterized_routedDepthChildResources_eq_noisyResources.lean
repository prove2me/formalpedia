-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthChildResources_eq_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:41:28.642572+00:00
-- url     : https://prove2.me/submissions/24ebf0f4-d129-4728-9627-b1086ad62565

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_eq_depthTwoChildResources
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_eq_noisyResources


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
    routedDepthChildResources h hdegree state port hhalf =
      noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf) := by
  rw [routedDepthChildResources_eq_depthTwoChildResources]
  exact depthTwoChildResources_eq_noisyResources h hdegree rate port hhalf
end QEC.Distillation.HH18Parameterized
