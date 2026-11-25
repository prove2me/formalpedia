-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.ofRealCoords_smul_centerCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:09.588699+00:00
-- url     : https://prove2.me/submissions/c93d4b8e-72a1-496d-8bfb-b83100bd9356

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord

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
theorem _root_.solution (s : ℝ) : unrealify (s • v0 r) = dz r ((s : ℂ) * Complex.I) := by
  ext i j
  apply Complex.ext
  · simp only [unrealify, v0, dz, diagonal_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = cI r
      · subst hi
        simp
      · simp [hi]
    · simp [hij]
  · simp only [unrealify, v0, dz, diagonal_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = cI r
      · subst hi
        simp
      · simp [hi]
    · simp [hij]
      intro hi hj
      exact absurd (hi.trans hj.symm) hij
end PI.ExistsGaugeMeasureForEachRank.W
