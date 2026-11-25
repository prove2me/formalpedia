-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.val_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:09.0051+00:00
-- url     : https://prove2.me/submissions/594775a8-e177-45f0-a8bc-f172a58a6277

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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]
omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] [DecidableEq κ]
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {x y : κ → k} (hx : ∀ p, valuation k (x p) ≤ 1) (hy : ∀ p, valuation k (y p) ≤ 1) : valuation k (x ⬝ᵥ y) ≤ 1 :=
  (valuation k).map_sum_le fun p _ => by rw [map_mul]; exact mul_le_one' (hx p) (hy p)
end PositivityTheory.ThKG.Std
