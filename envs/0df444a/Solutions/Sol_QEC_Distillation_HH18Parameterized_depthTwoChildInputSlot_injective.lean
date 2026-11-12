-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:10:09.498903+00:00
-- url     : https://prove2.me/submissions/02888373-cda5-4696-b632-8673e128c7f3

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Theorems.Thm_QEC_Distillation_DependentBatch_childInputSlot_injective


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
    (child : LogicalSite m w) :
    Function.Injective (depthTwoChildInputSlot m w child) := by
  intro left right hroute
  apply DependentBatch.childInputSlot_injective child
  apply (depthTwoRouting m w).injective
  exact hroute
end QEC.Distillation.HH18Parameterized
