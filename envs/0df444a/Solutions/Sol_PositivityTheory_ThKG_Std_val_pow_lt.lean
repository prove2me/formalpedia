-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.val_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:49.978785+00:00
-- url     : https://prove2.me/submissions/8fd4c705-b063-428a-b3a6-574d9b3df3da

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow

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
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hϖ : IsUnif ϖ) (hc : 1 ≤ c) : valuation k ((ϖ : k) ^ c) < 1 := by
  rw [map_pow]; exact pow_lt_one₀ zero_le (hϖ ▸ uniformizer_lt_one) (by omega)
end PositivityTheory.ThKG.Std
