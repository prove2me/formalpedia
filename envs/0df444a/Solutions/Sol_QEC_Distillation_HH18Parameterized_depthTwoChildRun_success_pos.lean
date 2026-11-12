-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildRun_success_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:48:09.622249+00:00
-- url     : https://prove2.me/submissions/9da03928-30a2-4e5d-8ccb-4bc9d61d6fdc

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildRun_eq_resourceDecodedRun
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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2) :
    0 < (depthTwoChildRun h hdegree epsilon child hhalf).successProbability := by
  rw [depthTwoChildRun_eq_resourceDecodedRun]
  exact endpointWeight_accepted_pos h hdegree
    (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)
end QEC.Distillation.HH18Parameterized
