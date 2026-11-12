-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoRouting_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:49:17.516647+00:00
-- url     : https://prove2.me/submissions/adab4f89-09d8-45bb-9457-d9f9faf69fcc

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
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w) :
    depthTwoRouting m w (parent, port) = (port, parent) :=
  rfl
end QEC.Distillation.HH18Parameterized
