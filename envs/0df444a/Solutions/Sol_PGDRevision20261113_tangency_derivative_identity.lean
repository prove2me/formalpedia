-- Prove2me | solution 1 for PGDRevision20261113.tangency_derivative_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:22:46.4666+00:00
-- url     : https://prove2.me/submissions/faabb04e-0139-4044-a139-fefbe36ca0e3

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open PGDRevision20261113

theorem solution : TangencyDerivativeIdentityClaim := by
  intro A B v w x hA hB hv hw hden hsame
  have hwden : w x + B x ≠ 0 := by simpa [hsame] using hden
  have hdw := ((hw.hasDerivAt.sub hA.hasDerivAt).div
    (hw.hasDerivAt.add hB.hasDerivAt) hwden).deriv
  have hdv := ((hv.hasDerivAt.sub hA.hasDerivAt).div
    (hv.hasDerivAt.add hB.hasDerivAt) hden).deriv
  change deriv ((w - A) / (w + B)) x - deriv ((v - A) / (v + B)) x = _
  rw [hdw, hdv]
  simp only [Pi.add_apply, Pi.sub_apply, hsame]
  field_simp
  <;> ring
