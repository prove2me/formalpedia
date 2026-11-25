-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.col_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:57.700868+00:00
-- url     : https://prove2.me/submissions/f26f5c83-4c9a-4703-b1f0-c7770f0c5bd9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_rev_eq_c_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Hpk_apply
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conjT_mul_H

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
theorem _root_.solution {g : Mat 0 r} (hg : g ∈ UWb 0 r) (q : Fin (2 * r + 0 + 1)) (hq : q ≠ cI r) :
    g q (cI r) = 0 := by
  have hp : Fin.rev q ≠ cI r := fun h => hq ((rev_eq_c_iff q).1 h)
  have hU : gᴴ * Hpk 0 r * g = Hpk 0 r := hg.1
  have h1 := congrFun (congrFun hU (Fin.rev q)) (cI r)
  rw [Matrix.mul_apply] at h1
  simp only [conjT_mul_H hg _ hp] at h1
  simp [Hpk_apply, Fin.rev_rev, hp, Ne.symm hq] at h1
  exact h1
end PI.ExistsGaugeMeasureForEachRank.W
