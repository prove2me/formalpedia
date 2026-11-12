-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildRun_eq_resourceDecodedRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:00:10.481467+00:00
-- url     : https://prove2.me/submissions/e4a78747-6b74-429c-8665-a138fc2488be

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    depthTwoChildRun h hdegree epsilon child hhalf =
      resourceDecodedRun h hdegree (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)) := by
  unfold depthTwoChildRun
  rw [depthTwoChildResources_eq_noisyResources]
end QEC.Distillation.HH18Parameterized
