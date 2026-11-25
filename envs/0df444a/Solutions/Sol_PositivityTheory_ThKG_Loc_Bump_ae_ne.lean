-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.ae_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:51.783261+00:00
-- url     : https://prove2.me/submissions/55015c0a-7d4c-4c53-ba35-d79795b2e899

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution : ∀ᵐ c : ι → ℂ, ∀ w, c w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure ℂ)) w).ae (p := fun z => z ≠ 0)
    (by rw [ae_iff]; simp)
end PositivityTheory.ThKG.Loc.Bump
