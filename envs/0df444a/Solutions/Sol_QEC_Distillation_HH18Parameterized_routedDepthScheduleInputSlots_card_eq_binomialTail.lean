-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleInputSlots_card_eq_binomialTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:02:13.424208+00:00
-- url     : https://prove2.me/submissions/69b30df1-78c3-4b72-a2be-4589d18c7050

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleInputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalInputCount_eq_binomialTail


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
theorem _root_.solution (m w depth : Nat) :
    Fintype.card (routedDepthScheduleInputSlots m w depth) =
      binomialTail m w ^ depth := by
  rw [routedDepthScheduleInputSlots_card, physicalInputCount_eq_binomialTail]
end QEC.Distillation.HH18Parameterized
