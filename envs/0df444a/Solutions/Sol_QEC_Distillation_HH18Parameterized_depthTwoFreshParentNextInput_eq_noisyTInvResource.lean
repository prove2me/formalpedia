-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoFreshParentNextInput_eq_noisyTInvResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:51:26.289214+00:00
-- url     : https://prove2.me/submissions/50fc58b2-cf6d-4138-85b3-cdc5a01faa83

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortDephasedNextInput_eq_noisyTInvResource
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon source.2 ≤ 1 / 2) :
    depthTwoFreshParentNextInput h hdegree epsilon source =
      HH18NoisyInput.noisyTInvResource
        (selectedLogicalPortNextInputRate h hdegree epsilon source.2 hhalf) := by
  rw [depthTwoFreshParentNextInput,
    depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput]
  exact selectedLogicalPortDephasedNextInput_eq_noisyTInvResource
    h hdegree epsilon source.2 hhalf
end QEC.Distillation.HH18Parameterized
