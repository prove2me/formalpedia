-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.aBasisErrorParameter_selectedLogicalPortNextInputRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:14:39.008219+00:00
-- url     : https://prove2.me/submissions/a3e8dd9d-3711-4837-9a7a-f43c12c48edd

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
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2) :
    aBasisErrorParameter
      (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf) =
      selectedLogicalPortRawParameter h hdegree epsilon port := by
  rfl
end QEC.Distillation.HH18Parameterized
