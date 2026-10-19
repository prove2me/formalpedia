-- Prove2me | solution 1 for TokenFinance.MoralHazard.token_expected_profit
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T11:08:28.433665+00:00
-- url     : https://prove2.me/submissions/5918f614-4379-4a19-a619-2983c59ed2f5

-- DS19C standalone copy of the partial MiMo6 solution for
-- TokenFinance.MoralHazard.token_expected_profit (theorem_id 54234c27-2d13-44a6-a7f5-ab83423cde2f).
-- Attribution: original file Solutions/Sol_MIMO6_TokenFinance_MoralHazard_token_expected_profit.lean
-- (MiMo6, interrupted by provider rate limit). DS19C inspected the mathematics, recompiled it
-- and checked the exact live statement; the proof below is unchanged and sorry-free.
-- MIMO6 solution for TokenFinance.MoralHazard.token_expected_profit
-- (theorem_id 54234c27-2d13-44a6-a7f5-ab83423cde2f), p. 31.
--
-- Statement: under the token contract with pre-sale t > 0 and monopoly output, the
-- entrepreneur's expected profit is c/(c+t) * 2/(3 theta) * ((theta - c)/2 - t)^3 when
-- c + 2t <= theta, and 0 when theta <= c + 2t.
--
-- Math. Pointwise in x, with q^m(x) = max((x-c)/2, 0):
--  * if x <= c + 2t then (x-c)/2 <= t and 0 <= t, so q^m(x) <= t and the branch t < q^m(x) is
--    false: the profit is 0; also (x-c-2t)/2 <= 0.
--  * if x > c + 2t then q^m(x) = (x-c)/2 > t, 1 - alpha_T = c/(c+t), x - q^m = (x+c)/2 and
--    q^m - t = (x-c-2t)/2, so the profit is
--      c/(c+t) * ((x-c-2t)/2) * ((x+c)/2) - c * ((x-c-2t)/2)
--    = c/(c+t) * ((x-c-2t)/2) * (((x+c)/2) - (c+t)) = c/(c+t) * ((x-c-2t)/2)^2.
-- Hence for every x: profit(x) = c/(c+t) * (max((x-c-2t)/2, 0))^2, a continuous function.
-- If theta <= c+2t it vanishes on [0, theta], so the expectation is 0. If c+2t <= theta, split
-- at m = c+2t: the integral over [0,m] vanishes and over [m,theta] the integrand equals the
-- polynomial c/(c+t) * (x-m)^2/4, with antiderivative c/(c+t)*(x-m)^3/12, giving
--   expect = [c/(c+t) * (theta-m)^3/12] / theta = c/(c+t) * 8((theta-c)/2 - t)^3 / (12 theta)
--          = c/(c+t) * 2/(3 theta) * ((theta-c)/2 - t)^3.
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

theorem solution (c t θ : ℝ) (hc : 0 < c) (ht : 0 < t) (hθ : 0 < θ) :
    (c + 2 * t ≤ θ →
      TokenFinance.Debt.expect θ
          (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) =
        c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3) ∧
    (θ ≤ c + 2 * t →
      TokenFinance.Debt.expect θ
          (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) = 0) := by
  have hct : 0 < c + t := by linarith
  have hctne : c + t ≠ 0 := ne_of_gt hct
  have hθne : θ ≠ 0 := ne_of_gt hθ
  -- Pointwise reduction of the integrand.
  have hpoint : ∀ x : ℝ, TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
      = c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 := by
    intro x
    unfold TokenFinance.Debt.tokEnt TokenFinance.Debt.qm TokenFinance.Debt.alphaT
    by_cases h : c + 2 * t < x
    · have hxc : c < x := by linarith
      have hq : max ((x - c) / 2) 0 = (x - c) / 2 :=
        max_eq_left (div_nonneg (sub_nonneg_of_le hxc.le) (by norm_num))
      have hgt : t < max ((x - c) / 2) 0 := by rw [hq]; linarith
      rw [if_pos hgt, hq]
      have hmax : max ((x - c - 2 * t) / 2) 0 = (x - c - 2 * t) / 2 :=
        max_eq_left (div_nonneg (by linarith) (by norm_num))
      rw [hmax]
      field_simp [hctne]
      ring
    · have hle : x ≤ c + 2 * t := le_of_not_gt h
      have hqle : max ((x - c) / 2) 0 ≤ t := max_le (by linarith) (le_of_lt ht)
      have hng : ¬t < max ((x - c) / 2) 0 := by linarith
      rw [if_neg hng]
      have hm2 : max ((x - c - 2 * t) / 2) 0 = 0 := max_eq_right (by linarith)
      rw [hm2]
      ring
  have hFcont : Continuous fun x : ℝ => c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 := by
    fun_prop
  have hGbcont : Continuous fun x : ℝ => c / (c + t) * ((x - (c + 2 * t)) / 2) ^ 2 := by
    fun_prop
  refine ⟨?_, ?_⟩
  · intro hc1
    have h0m : 0 < c + 2 * t := by linarith
    have hcong : ∫ x in (0 : ℝ)..θ,
        TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
        = ∫ x in (0 : ℝ)..θ, c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => hpoint x)
    have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) (c + 2 * t),
        c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 = 0 := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : max ((x - c - 2 * t) / 2) 0 = 0 := max_eq_right (by linarith)
        rw [this]; ring
      · have : max ((x - c - 2 * t) / 2) 0 = 0 := max_eq_right (by linarith)
        rw [this]; ring
    have hzero : ∫ x in (0 : ℝ)..(c + 2 * t),
        c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr hzeroAux]
      exact intervalIntegral.integral_zero
    have hcong2 : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
        c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2
          = c / (c + t) * ((x - (c + 2 * t)) / 2) ^ 2 := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hge : 0 ≤ (x - c - 2 * t) / 2 := by linarith
        rw [max_eq_left hge]; ring
      · have hge : 0 ≤ (x - c - 2 * t) / 2 := by linarith
        rw [max_eq_left hge]; ring
    have hsplit : (∫ x in (0 : ℝ)..(c + 2 * t), c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2)
          + (∫ x in (c + 2 * t)..θ, c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2)
        = ∫ x in (0 : ℝ)..θ, c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        (hFcont.intervalIntegrable _ _) (hFcont.intervalIntegrable _ _)
    have hG : ∀ y : ℝ, HasDerivAt
        (fun z : ℝ => c / (c + t) * (z - (c + 2 * t)) ^ 3 / 12)
        (c / (c + t) * ((y - (c + 2 * t)) / 2) ^ 2) y := by
      intro y
      have h1 : HasDerivAt (fun z : ℝ => (z - (c + 2 * t)) ^ 3)
          ((3 : ℕ) * (y - (c + 2 * t)) ^ ((3 : ℕ) - 1) * 1) y :=
        (hasDerivAt_id y).sub_const (c + 2 * t) |>.pow 3
      have hval2 : c / (c + t) * ((3 : ℕ) * (y - (c + 2 * t)) ^ ((3 : ℕ) - 1) * 1) / 12
          = c / (c + t) * ((y - (c + 2 * t)) / 2) ^ 2 := by
        norm_num
        field_simp [hctne]
        ring
      rw [show c / (c + t) * ((y - (c + 2 * t)) / 2) ^ 2
          = c / (c + t) * ((3 : ℕ) * (y - (c + 2 * t)) ^ ((3 : ℕ) - 1) * 1) / 12 by
        exact hval2.symm]
      exact (h1.const_mul (c / (c + t))).div_const 12
    have hFTC : ∫ x in (c + 2 * t)..θ, c / (c + t) * ((x - (c + 2 * t)) / 2) ^ 2
        = c / (c + t) * (θ - (c + 2 * t)) ^ 3 / 12
          - c / (c + t) * ((c + 2 * t) - (c + 2 * t)) ^ 3 / 12 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => hG y) (hGbcont.intervalIntegrable _ _)
    have hmid : c / (c + t) * ((c + 2 * t) - (c + 2 * t)) ^ 3 / 12 = 0 := by ring
    have hnum : c / (c + t) * (θ - (c + 2 * t)) ^ 3 / 12
        = c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 * θ := by
      field_simp [hctne, hθne]
      ring
    simp only [TokenFinance.Debt.expect]
    rw [hcong, ← hsplit, hzero, zero_add, intervalIntegral.integral_congr hcong2, hFTC,
      hmid, sub_zero, div_eq_iff hθne]
    exact hnum
  · intro hc2
    have hcong : ∫ x in (0 : ℝ)..θ,
        TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
        = ∫ x in (0 : ℝ)..θ, c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => hpoint x)
    have hzeroAux : ∀ x ∈ Set.uIcc (0 : ℝ) θ,
        c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 = 0 := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : max ((x - c - 2 * t) / 2) 0 = 0 := max_eq_right (by linarith)
        rw [this]; ring
      · have : max ((x - c - 2 * t) / 2) 0 = 0 := max_eq_right (by linarith)
        rw [this]; ring
    have hzero : ∫ x in (0 : ℝ)..θ, c / (c + t) * (max ((x - c - 2 * t) / 2) 0) ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr hzeroAux]
      exact intervalIntegral.integral_zero
    simp only [TokenFinance.Debt.expect]
    rw [hcong, hzero]
    simp
