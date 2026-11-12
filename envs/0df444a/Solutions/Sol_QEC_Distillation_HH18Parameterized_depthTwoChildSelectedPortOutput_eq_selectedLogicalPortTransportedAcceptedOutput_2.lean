-- Prove2me | solution 2 for QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:35:11.863849+00:00
-- url     : https://prove2.me/submissions/8c46352c-6c58-4e9f-b96c-eba2a410be85

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildRun_eq_resourceDecodedRun

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
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortOutput h hdegree epsilon child hhalf port =
      selectedLogicalPortTransportedAcceptedOutput h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by
  unfold depthTwoChildSelectedPortOutput
  rw [depthTwoChildRun_eq_resourceDecodedRun]
  rfl
end QEC.Distillation.HH18Parameterized
