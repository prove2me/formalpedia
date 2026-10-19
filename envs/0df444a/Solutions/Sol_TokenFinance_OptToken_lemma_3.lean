-- Prove2me | solution 1 for TokenFinance.OptToken.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:27:09.817055+00:00
-- url     : https://prove2.me/submissions/ac2ce513-8604-440a-82c4-b85564c1235d

-- MIMO3 solution for TokenFinance.OptToken.lemma_3 (theorem_id 17ad5e8a-7935-4fe6-927b-34f38eb95d68)
-- Lemma 3 / equations (11)-(12), Malinova & Park. With revenue share alpha_t = t/(c+t)
-- one has 0 < alpha_t < 1, and for q^m(x) = (x-c)/2 > t the payoff
--   g(q) = (1-alpha_t)(q-t)(x-q) - c*q
-- is maximized at q = q^m(x). Algebra: g is a concave quadratic in q with vertex at
--   q* = (x+t)/2 - c/(2(1-alpha_t)) = (x+t)/2 - (c+t)/2 = (x-c)/2,
-- exactly (11)-(12); equivalently the exact identity
--   g(q) = g(q^m) - (c/(c+t)) * (q - q^m)^2
-- with positive coefficient c/(c+t) = 1 - alpha_t gives the inequality at once.
import Definitions.Def_TokenFinance_Debt_Setting

open TokenFinance.Debt

theorem solution (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    0 < TokenFinance.Debt.alphaT c t ∧ TokenFinance.Debt.alphaT c t < 1 ∧
      ∀ x q : ℝ, t < (x - c) / 2 → t < q →
        (1 - TokenFinance.Debt.alphaT c t) * (q - t) * (x - q) - c * q ≤
          (1 - TokenFinance.Debt.alphaT c t) * ((x - c) / 2 - t) * (x - (x - c) / 2) -
            c * ((x - c) / 2) := by
  have hct : 0 < t + c := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- 0 < alpha_t from 0 < t and 0 < t + c
    rw [TokenFinance.Debt.alphaT]
    exact div_pos ht hct
  · -- alpha_t < 1 since t < t + c
    rw [TokenFinance.Debt.alphaT]
    rw [div_lt_one hct]
    linarith
  · intro x q hqm hq
    simp only [TokenFinance.Debt.alphaT]
    -- completing the square for the concave quadratic g
    have key : (1 - t / (t + c)) * (q - t) * (x - q) - c * q =
        (1 - t / (t + c)) * ((x - c) / 2 - t) * (x - (x - c) / 2) - c * ((x - c) / 2) -
          (q - (x - c) / 2) ^ 2 * (c / (t + c)) := by
      field_simp [hct.ne']
      ring
    have hmul : 0 ≤ (q - (x - c) / 2) ^ 2 * (c / (t + c)) :=
      mul_nonneg (sq_nonneg _) (div_pos hc hct).le
    linarith [key, hmul]
