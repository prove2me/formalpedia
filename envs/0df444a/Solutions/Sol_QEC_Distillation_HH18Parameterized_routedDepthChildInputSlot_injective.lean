-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:53:20.975216+00:00
-- url     : https://prove2.me/submissions/259c386c-bdc1-4665-85df-eddc4e3f1a65

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_injective


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
theorem _root_.solution (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w) :
    Function.Injective (routedDepthChildInputSlot m w depth pathPrefix child) := by
  intro left right hroute
  apply depthTwoChildInputSlot_injective m w child
  exact congrArg Prod.snd hroute
end QEC.Distillation.HH18Parameterized
