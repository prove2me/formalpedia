-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleOutputSlots_card_eq_binomialUpTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:02:17.040196+00:00
-- url     : https://prove2.me/submissions/8773673d-e5df-4927-86a6-551641b463d0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleOutputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_logicalOutputCount_eq_binomialUpTo


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
    Fintype.card (routedDepthScheduleOutputSlots m w depth) =
      binomialUpTo m w ^ depth := by
  rw [routedDepthScheduleOutputSlots_card, logicalOutputCount_eq_binomialUpTo]
end QEC.Distillation.HH18Parameterized
