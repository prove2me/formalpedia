-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthOutputSlots_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:46:12.444076+00:00
-- url     : https://prove2.me/submissions/6d6a7d7a-0da3-4f21-9fe8-890ae46f1374

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthOutputSlots_nonempty

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
    0 < Fintype.card (routedDepthOutputSlots m w depth) :=
  Fintype.card_pos_iff.mpr (routedDepthOutputSlots_nonempty m w depth)
end QEC.Distillation.HH18Parameterized
