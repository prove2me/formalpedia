-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.ind_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:53.36798+00:00
-- url     : https://prove2.me/submissions/15292176-9aff-4165-9fe0-67613e379622

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {c x y : k} (hy : valuation k y ≤ valuation k c) : ind c (x + y) = ind c x := by
  unfold ind
  refine if_congr ⟨fun h => ?_, fun h => Valuation.map_add_le _ h hy⟩ rfl rfl
  have := (valuation k).map_sub_le h hy
  rwa [add_sub_cancel_right] at this
end PositivityTheory.ThKG.Std
