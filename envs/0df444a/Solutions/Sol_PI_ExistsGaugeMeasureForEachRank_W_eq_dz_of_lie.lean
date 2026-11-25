-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.eq_dz_of_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:10.27006+00:00
-- url     : https://prove2.me/submissions/a8a77e92-961e-4c07-8144-cbb7e9a1e900

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_entry_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) : X = dz r (X (cI r) (cI r)) := by
  ext i j
  by_cases h : i = cI r ∧ j = cI r
  · obtain ⟨rfl, rfl⟩ := h
    simp [dz]
  · rw [entry_zero hX i j h, dz, diagonal_apply]
    split_ifs with hij
    · subst hij
      have hi : i ≠ cI r := fun hi => h ⟨hi, hi⟩
      simp [hi]
    · rfl
end PI.ExistsGaugeMeasureForEachRank.W
