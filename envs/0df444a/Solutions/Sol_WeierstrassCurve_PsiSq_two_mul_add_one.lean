-- Prove2me | solution 1 for WeierstrassCurve.PsiSq_two_mul_add_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:32.011776+00:00
-- url     : https://prove2.me/submissions/b8a560df-2251-4430-832d-0bc59aaa61d1

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDiffAddCert
import Definitions.Def_WardSomos
import Definitions.Def_PsiInvariant

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_DifferentialAddition` and their helpers. -/

open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Denominator identity: `ΨSq(2m+1) = deltaP²`, purely definitional via `ΨSq_odd`. -/
theorem _root_.solution (W : WeierstrassCurve R) (m : ℤ) :
    W.ΨSq (2 * m + 1)
      = diffAddDenP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) := by
  by_cases hm : Even m
  · have hm1 : ¬ Even (m + 1) := by simp [Int.even_add_one, hm]
    rw [W.ΨSq_odd m]
    simp only [diffAddDenP, deltaP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      if_pos hm, if_neg hm1, show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring]
    ring
  · have hm1 : Even (m + 1) := by simpa [Int.even_add_one, Int.not_even_iff_odd] using hm
    rw [W.ΨSq_odd m]
    simp only [diffAddDenP, deltaP, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
      if_neg hm, if_pos hm1, show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring]
    ring

end

end WeierstrassCurve
