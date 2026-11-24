-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.IsPsi.ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:57.790021+00:00
-- url     : https://prove2.me/submissions/c8efb474-2fd6-4f48-8fc2-7d08b8ec40e8

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
omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThKG.Std
namespace IsPsi
theorem _root_.solution {ψ : AddChar k ℂ} (h : IsPsi ψ) {x : k} (hx : ¬ valuation k x ≤ 1) : ∃ y, valuation k y ≤ 1 ∧ ψ (x * y) ≠ 1 := by
  by_contra h'
  push Not at h'
  exact hx ((h.cond x).1 h')
end IsPsi
end PositivityTheory.ThKG.Std
