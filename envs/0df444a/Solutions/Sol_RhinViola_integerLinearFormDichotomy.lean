-- Prove2me | solution 1 for RhinViola.integerLinearFormDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T16:23:55.615692+00:00
-- url     : https://prove2.me/submissions/5bb0437d-5ee0-40fd-b745-eb3124bf6241

import Theorems.Thm_RhinViola_nonzeroDeterminantSeparation
import Theorems.Thm_RhinViola_zeroDeterminantIdentity

theorem solution
    (α f : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q) (hb : b ≠ 0)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2) :
    |α - (p : ℝ) / (q : ℝ)| = |f| / |(b : ℝ)| ∨
      (1 : ℝ) / 2 ≤ |(b : ℝ)| * (q : ℝ) *
        |α - (p : ℝ) / (q : ℝ)| := by
  by_cases hdet : (q : ℤ) * a = p * b
  · exact Or.inl <|
      RhinViola.zeroDeterminantIdentity α f a b p q hq hb hf hdet
  · exact Or.inr <|
      RhinViola.nonzeroDeterminantSeparation α f a b p q hq hf hsmall hdet
