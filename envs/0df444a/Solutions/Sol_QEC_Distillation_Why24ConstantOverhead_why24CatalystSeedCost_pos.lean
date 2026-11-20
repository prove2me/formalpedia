-- Prove2me | solution 1 for QEC.Distillation.Why24ConstantOverhead.why24CatalystSeedCost_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:51:22.34431+00:00
-- url     : https://prove2.me/submissions/213df083-d665-4eef-aa5a-5bc685d30318

import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
import Definitions.Def_QEC_Results_Distillation_ConstantOverhead
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathSchedule_yield_pos
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedInputSlot_card
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PathTypedOutputSlot_card


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24ConstantOverhead
open Filter Topology
open Semantics
open Why24AGFamily Why24OneRoundProtocol
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open Triorthogonal.BH12Concatenation
open Triorthogonal.BH12EvenFamily
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12Protocol
namespace QEC.Distillation.Why24ConstantOverhead
theorem _root_.solution : 0 < why24CatalystSeedCost := by
  have hyield := bh12PathSchedule_yield_pos 1 why24CatalystSeedParameter
    why24CatalystSeedParameter_small why24CatalystSeedParameter_le_half
    why24CatalystSeedParameter_strong why24CatalystSeedScheduleIndex
  have hinput :
      (Fintype.card
        (bh12PathScheduleInputSlots 1 why24CatalystSeedScheduleIndex) : Real) = 14 := by
    change (Fintype.card (depthRawInputPath 1 1) : Real) = 14
    rw [bh12PathTypedInputSlot_card]
    norm_num [bh12InputCount, resourceCount, Column, logicalCount]
  have houtput :
      (Fintype.card
        (bh12PathScheduleOutputSlots 1 why24CatalystSeedScheduleIndex) : Real) = 2 := by
    change (Fintype.card (depthOutputPath 1 1) : Real) = 2
    rw [bh12PathTypedOutputSlot_card]
    norm_num [bh12OutputCount, logicalCount]
  unfold why24CatalystSeedCost bh12PathScheduleTypedSuccessfulOutputCost
    DependentBatch.typedSuccessfulOutputCost DependentBatch.typedInputOutputRatio
  rw [hinput, houtput]
  exact div_pos (by norm_num) hyield
end QEC.Distillation.Why24ConstantOverhead
