-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.eq_dgl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:03.628718+00:00
-- url     : https://prove2.me/submissions/f7462aba-8d6e-4ea6-bed4-7bc655241c29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_apply
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_col_fix
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_col_c

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
theorem _root_.solution {g : Mat 0 r} (hg : g ∈ UWb 0 r) : g = dgl r (g (cI r) (cI r)) := by
  ext i j
  rw [dgl_apply]
  by_cases hj : j = cI r
  · subst hj
    by_cases hi : i = cI r
    · subst hi
      simp
    · rw [col_c hg i hi]
      simp [hi]
  · rw [col_fix hg j hj i]
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij]
end PI.ExistsGaugeMeasureForEachRank.W
