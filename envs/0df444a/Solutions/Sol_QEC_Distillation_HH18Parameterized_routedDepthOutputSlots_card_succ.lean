-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:53:06.860592+00:00
-- url     : https://prove2.me/submissions/10c5c376-ecb1-447d-8bc4-d41b05aba17b

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_card

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
    Fintype.card (routedDepthOutputSlots m w (depth + 1)) =
      Fintype.card (routedDepthOutputSlots m w depth) * logicalOutputCount m w := by
  rw [routedDepthOutputSlots_card, routedDepthOutputSlots_card]
  exact pow_succ _ _
end QEC.Distillation.HH18Parameterized
