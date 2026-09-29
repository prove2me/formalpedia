-- Prove2me | solution 1 for Schanuel.hermite_lindemann
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T18:50:49.675423+00:00
-- url     : https://prove2.me/submissions/ad225f4c-ea36-43e6-94e7-0de7b2c399d1

import Theorems.Thm_Schanuel_lindemann_weierstrass

/-- **Hermite–Lindemann from Lindemann–Weierstrass.**
If `a` is a nonzero algebraic number then `exp a` is transcendental: otherwise the relation
`(-exp a) * exp 0 + 1 * exp a = 0` would be a nontrivial vanishing linear combination of
`exp` at the distinct algebraic points `0` and `a` with algebraic coefficients, contradicting
the Lindemann–Weierstrass theorem. -/
theorem solution (a : ℂ) (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) :
    Transcendental ℚ (Complex.exp a) := by
  intro halg
  have hne := Schanuel.lindemann_weierstrass 2 ![0, a] ![-Complex.exp a, 1]
    (by
      intro i
      fin_cases i
      · exact isAlgebraic_zero
      · exact ha)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    (by
      intro i
      fin_cases i
      · exact halg.neg
      · exact isAlgebraic_one)
    ⟨1, by simp⟩
  apply hne
  simp [Fin.sum_univ_two]
