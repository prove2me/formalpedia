-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthSuccessorRate_le_two_mul_acceptedResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:57:19.502181+00:00
-- url     : https://prove2.me/submissions/33f3f1fe-0814-43ba-b16d-d461a88f6c37

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    (selectedLogicalPortNextInputRate h hdegree rate port hhalf).1 ≤
      2 * acceptedResidualError h hdegree rate := by
  change selectedLogicalPortRawError h hdegree rate port ≤ _
  exact selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree rate port
end QEC.Distillation.HH18Parameterized
