-- Prove2me | solution 1 for PGDRevision20261113.quadratic_envelope_identities
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T08:08:38.088847+00:00
-- url     : https://prove2.me/submissions/be720bea-c0c9-4dd4-b4b5-bc2c0f57fe0c

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open PGDRevision20261113

theorem solution : QuadraticEnvelopeIdentitiesClaim := by
  intro u hu
  have hpos : 0 < 2 - u := by linarith [hu.2]
  have hne : 10 * (2 - u) ≠ 0 := ne_of_gt (by positivity)
  have hp : quadraticEnvelopeError u + 1 / 10 = u * (10 - 9 * u) / (10 * (2 - u)) := by
    dsimp [quadraticEnvelopeError]
    field_simp
    <;> ring
  have hm : 1 / 10 - quadraticEnvelopeError u = (3 * u - 2) ^ 2 / (10 * (2 - u)) := by
    dsimp [quadraticEnvelopeError]
    field_simp
    <;> ring
  refine ⟨hp, hm, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hnum : 0 ≤ u * (10 - 9 * u) := mul_nonneg hu.1 (by linarith [hu.2])
    have hdiv : 0 ≤ u * (10 - 9 * u) / (10 * (2 - u)) := div_nonneg hnum (by positivity)
    linarith
  · have hdiv : 0 ≤ (3 * u - 2) ^ 2 / (10 * (2 - u)) := div_nonneg (sq_nonneg _) (by positivity)
    linarith
