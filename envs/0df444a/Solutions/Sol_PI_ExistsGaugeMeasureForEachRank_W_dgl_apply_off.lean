-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.dgl_apply_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:58.227981+00:00
-- url     : https://prove2.me/submissions/f138f4be-a4e8-421d-9b31-fdd5da04ae99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (u : ℂ) (i j : Fin (2 * r + 0 + 1)) (h : ¬ (i = cI r ∧ j = cI r)) :
    dgl r u i j = (1 : Mat 0 r) i j := by
  rw [dgl_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have hi : i ≠ cI r := fun hi => h ⟨hi, hi⟩
    simp [hi]
  · simp [hij]
end PI.ExistsGaugeMeasureForEachRank.W
