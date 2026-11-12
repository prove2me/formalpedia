-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortRawError_eq_selectedLogicalPortRawError
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:14:31.579871+00:00
-- url     : https://prove2.me/submissions/a0119bb8-b26e-44fb-8f4e-ca2eac97f859

import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
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

theorem solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (child : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon child ≤ 1 / 2)
    (port : LogicalSite m w) :
    depthTwoChildSelectedPortRawError h hdegree epsilon child hhalf port =
      selectedLogicalPortRawError h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by
  unfold depthTwoChildSelectedPortRawError
  rw [depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput]
  rfl