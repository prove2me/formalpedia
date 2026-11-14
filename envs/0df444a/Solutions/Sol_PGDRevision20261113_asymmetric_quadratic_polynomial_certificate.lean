-- Prove2me | solution 1 for PGDRevision20261113.asymmetric_quadratic_polynomial_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T08:09:33.499225+00:00
-- url     : https://prove2.me/submissions/d8a2789e-a5d6-4f35-aa2d-b17151d861dd

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open PGDRevision20261113

theorem solution : AsymmetricQuadraticPolynomialIdentityClaim := by
  intro u
  have hidentity : (3 - 2 * u) ^ 2 - 32 * u * (1 - u) ^ 2 =
      (1 - 2 * u) ^ 2 * (9 - 8 * u) := by ring
  refine ⟨hidentity, ?_⟩
  intro hu
  rw [hidentity]
  exact mul_nonneg (sq_nonneg _) (by linarith [hu.2])
