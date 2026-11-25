-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.integrable_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:56.342922+00:00
-- url     : https://prove2.me/submissions/69983c67-b9a0-46b4-822a-152d246b36ff

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


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
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {m : Measure k} (hm : IsVol m) {Φ : (κ → k) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (κ → k)) :
    Integrable Φ (Measure.pi fun _ : κ => m) := by
  haveI := hm.haar
  exact hΦ.1.continuous.integrable_of_hasCompactSupport hΦ.2
end PositivityTheory.ThKG.Std
