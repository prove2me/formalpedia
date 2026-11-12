-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildResources_eq_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:56:30.955695+00:00
-- url     : https://prove2.me/submissions/b18626d9-321f-4aaf-a408-d4b4ad0961d5

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoFreshParentNextInput_eq_noisyTInvResource

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
    depthTwoChildResources h hdegree epsilon child hhalf =
      noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf) := by
  funext parent
  change depthTwoFreshParentNextInput h hdegree epsilon (parent, child) =
    HH18NoisyInput.noisyTInvResource
      (selectedLogicalPortNextInputRate h hdegree epsilon child hhalf)
  exact depthTwoFreshParentNextInput_eq_noisyTInvResource h hdegree epsilon
    (parent, child) hhalf
end QEC.Distillation.HH18Parameterized
