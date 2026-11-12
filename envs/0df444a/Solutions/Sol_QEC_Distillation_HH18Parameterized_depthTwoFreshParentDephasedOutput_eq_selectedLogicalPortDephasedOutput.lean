-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoFreshParentDephasedOutput_eq_selectedLogicalPortDephasedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:11:16.35739+00:00
-- url     : https://prove2.me/submissions/912ebc16-6ed0-4200-b9c4-0cfe24c55f6c

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
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (source : depthTwoParentOutputSlots m w) :
    depthTwoFreshParentDephasedOutput h hdegree epsilon source =
      selectedLogicalPortDephasedOutput h hdegree epsilon source.2 := by
  rfl
end QEC.Distillation.HH18Parameterized
