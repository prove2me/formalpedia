-- Prove2me | solution 1 for TokenFinance.OptToken.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:42:09.201301+00:00
-- url     : https://prove2.me/submissions/e40722a7-788b-4b12-b194-d323595fd23f

-- MIMO2 solution for TokenFinance.OptToken.eq_15 (theorem_id f6dc0d95-45ec-4e94-b004-5e7839555680)
-- Case 2 of the token contract: if the monopoly quantity (x-c)/2 does not exceed the
-- pre-sale t, then the entrepreneur's profit at the (truncated) monopoly quantity is 0,
-- and every q > t yields a strictly negative profit.
-- Algebra: for q > t, tokEnt = (1 - t/(t+c))(q-t)(x-q) - c(q-t) = c(q-t)(x-q-c-t)/(c+t);
-- with x <= c + 2t and q > t the factor (x-q-c-t) <= t - q < 0, so the whole is < 0.
import Definitions.Def_TokenFinance_Debt_Setting

open TokenFinance.Debt

theorem solution (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    ∀ x : ℝ, (x - c) / 2 ≤ t →
      TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = 0 ∧
      ∀ q : ℝ, t < q → TokenFinance.Debt.tokEnt c t x q < 0 := by
  intro x hx
  have hcox : 0 < c + t := add_pos hc ht
  have hx2 : x ≤ c + 2 * t := by linarith
  -- the truncated monopoly quantity never exceeds t
  have hqm : TokenFinance.Debt.qm c x ≤ t := by
    unfold TokenFinance.Debt.qm
    exact max_le hx (le_of_lt ht)
  refine ⟨?_, fun q hq => ?_⟩
  · simp only [TokenFinance.Debt.tokEnt]
    rw [if_neg (not_lt.mpr hqm)]
  · simp only [TokenFinance.Debt.tokEnt]
    rw [if_pos hq]
    -- demand minus output stays below the effective cost c + t
    have hdiff : x - q < c + t := by
      calc x - q ≤ (c + 2 * t) - q := sub_le_sub_right hx2 q
        _ < (c + 2 * t) - t := sub_lt_sub_left hq _
        _ = c + t := by ring
    -- exact factorization of the profit
    have key : (1 - TokenFinance.Debt.alphaT c t) * (q - t) * (x - q) - c * (q - t)
        = c * (q - t) * (x - q - c - t) / (c + t) := by
      rw [TokenFinance.Debt.alphaT]
      field_simp [hcox.ne']
      ring
    rw [key]
    have hsplit : x - q - c < t := by linarith
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos hc (sub_pos.mpr hq)) (sub_neg_of_lt hsplit))
      hcox
