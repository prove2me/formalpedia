-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildSelectedPortOutput_eq_selectedLogicalPortTransportedAcceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:11:44.088025+00:00
-- url     : https://prove2.me/submissions/5bfbed1a-f4f0-4f5d-aba5-907d0f41e31a

import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildRun_eq_resourceDecodedRun
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
    depthTwoChildSelectedPortOutput h hdegree epsilon child hhalf port =
      selectedLogicalPortTransportedAcceptedOutput h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) port := by
  unfold depthTwoChildSelectedPortOutput
  rw [depthTwoChildRun_eq_resourceDecodedRun]
  rfl