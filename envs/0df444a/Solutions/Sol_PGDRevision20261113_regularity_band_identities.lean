-- Prove2me | solution 1 for PGDRevision20261113.regularity_band_identities
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T08:09:36.349204+00:00
-- url     : https://prove2.me/submissions/c0dea8ef-45a9-46a4-adc8-d3aba49ee5c6

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open PGDRevision20261113

theorem solution : RegularityBandIdentitiesClaim := by
  intro x hx
  have hpoly : regularityCurvature x = (29 + 11 * x + 11 * x ^ 2 + 29 * x ^ 3) / 180 := by
    by_cases hleft : x ≤ -1
    · have heq : x = -1 := by linarith [hx.1]
      subst x
      norm_num [regularityCurvature]
    · simp [regularityCurvature, hleft, hx.2]
  have hp : regularityCurvature x - (1 - x ^ 2) / 10 = (x + 1) * (11 + 29 * x ^ 2) / 180 := by
    rw [hpoly]
    ring
  have hm : 2 * (1 + x ^ 2) / 9 - regularityCurvature x = (1 - x) * (11 + 29 * x ^ 2) / 180 := by
    rw [hpoly]
    ring
  have hfactor : 0 ≤ 11 + 29 * x ^ 2 := by positivity
  have hl : 0 ≤ (x + 1) * (11 + 29 * x ^ 2) / 180 :=
    div_nonneg (mul_nonneg (by linarith [hx.1]) hfactor) (by norm_num)
  have hu : 0 ≤ (1 - x) * (11 + 29 * x ^ 2) / 180 :=
    div_nonneg (mul_nonneg (by linarith [hx.2]) hfactor) (by norm_num)
  exact ⟨hp, hm, by linarith, by linarith⟩
