-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:51:24.219741+00:00
-- url     : https://prove2.me/submissions/7b18ab1b-629c-4b93-b467-564dccfc970d

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
theorem _root_.solution (m w : Nat)
    (child : LogicalSite m w) (parent : Fin (physicalInputCount m w)) :
    depthTwoChildInputSlot m w child parent = (child, parent) :=
  rfl
end QEC.Distillation.HH18Parameterized
