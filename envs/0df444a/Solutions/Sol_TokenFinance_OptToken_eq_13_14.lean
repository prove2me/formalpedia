-- Prove2me | solution 1 for TokenFinance.OptToken.eq_13_14
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:27:08.68988+00:00
-- url     : https://prove2.me/submissions/3fd2797a-90b4-451f-b78b-20cf16883e73

-- MIMO3 solution for TokenFinance.OptToken.eq_13_14 (theorem_id baca39bc-e5a8-4897-a645-e7da557495a8)
-- Equations (13)-(14), Malinova & Park: for output q above the pre-sale t the entrepreneur's
-- realized token-contract payoff factors as
--   pi^e_t(x,q) = c/(c+t) * (q-t) * (x-q-c-t).
-- At the monopoly quantity q^m(x) = (x-c)/2 > t this reads
--   pi^e_t(x,q^m(x)) = c/(c+t) * ((x-c)/2 - t)^2 > 0,
-- since x - q^m - c - t = (x-c)/2 - t there and both factors are nonzero/positive.
import Definitions.Def_TokenFinance_Debt_Setting

open TokenFinance.Debt

theorem solution (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    (∀ x q : ℝ, t < q →
        TokenFinance.Debt.tokEnt c t x q = c / (c + t) * (q - t) * (x - q - c - t)) ∧
    (∀ x : ℝ, t < (x - c) / 2 →
        TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) =
          c / (c + t) * ((x - c) / 2 - t) ^ 2 ∧
        0 < TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) := by
  have hcox : 0 < c + t := add_pos hc ht
  refine ⟨?_, fun x hx => ?_⟩
  · -- (13): unfold the contract payoff on the branch t < q and factor over c + t
    intro x q hq
    simp only [TokenFinance.Debt.tokEnt]
    rw [if_pos hq]
    rw [TokenFinance.Debt.alphaT]
    field_simp [hcox.ne']
    ring
  · -- the monopoly quantity is untruncated here: (x-c)/2 > t > 0
    have hmid : 0 < (x - c) / 2 := lt_trans ht hx
    have hqm : TokenFinance.Debt.qm c x = (x - c) / 2 := max_eq_left hmid.le
    have hsq : TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) =
        c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
      rw [hqm]
      simp only [TokenFinance.Debt.tokEnt]
      rw [if_pos hx]
      rw [TokenFinance.Debt.alphaT]
      field_simp [hcox.ne']
      ring
    refine ⟨hsq, ?_⟩
    rw [hsq]
    have hpos : 0 < (x - c) / 2 - t := by linarith
    exact mul_pos (div_pos hc hcox) (sq_pos_of_ne_zero (ne_of_gt hpos))
