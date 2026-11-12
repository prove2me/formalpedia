-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthChildRun_eq_resourceDecodedRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:45:29.425478+00:00
-- url     : https://prove2.me/submissions/e7dc68f0-7be6-4ab2-8e62-af84adc06a7a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_eq_noisyResources

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
    routedDepthChildRun h hdegree state port hhalf =
      resourceDecodedRun h hdegree (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree rate port hhalf)) := by
  unfold routedDepthChildRun
  rw [routedDepthChildResources_eq_noisyResources]
end QEC.Distillation.HH18Parameterized
