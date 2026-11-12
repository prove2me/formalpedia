-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortRawError_le_two_mul_acceptedResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:42:33.263703+00:00
-- url     : https://prove2.me/submissions/956fe239-b384-4dd5-b9dc-435621aedf9e

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortRawError_le_two_mul_acceptedResidual


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
    depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port ≤
      2 * acceptedResidualError h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by
  rw [depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError]
  exact selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree
    (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port
end QEC.Distillation.HH18Parameterized
