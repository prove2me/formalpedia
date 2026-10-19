-- Prove2me | solution 1 for TokenFinance.OptToken.eq_16_lhs
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T21:03:22.442211+00:00
-- url     : https://prove2.me/submissions/aca4319d-a187-44b5-b434-d659544efa12

-- MIMO4 solution for TokenFinance.OptToken.eq_16_lhs (theorem_id c004fe9a-2b9e-41ae-b74c-406ad3bd42d7)
-- Equation (16)'s left side: the entrepreneur's expected profit under the token contract.
-- With q = q^m(x) = max((x-c)/2, 0) and 0 <= t, tokEnt c t x q^m(x) vanishes whenever
-- x <= c + 2t (there q^m <= t, so the definition takes its zero branch), while for
-- x > c + 2t it equals (c/(c+t))((x-c)/2 - t)^2, because 1 - alpha_t = c/(c+t),
-- x - q^m = (x+c)/2 and (x+c)/2 - (c+t) = (x-c)/2 - t. Both cases are summarised by the
-- single identity
--   tokEnt c t x q^m(x) = (c/(c+t)) (max ((x - (c+2t))/2, 0))^2 .       (*)
-- The right-hand side of (*) is continuous, so the integral over [0, theta] splits at
-- c+2t; the lower piece vanishes, and the upper piece (where the max is the identity)
-- integrates against the antiderivative (2/3)((x-c)/2 - t)^3 of ((x-c)/2 - t)^2, giving
-- (c/(c+t))(2/3)((theta-c)/2 - t)^3. Dividing by theta yields the claim.
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

theorem solution (c θ t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) (hupper : c + 2 * t ≤ θ) :
    TokenFinance.Debt.expect θ (fun x => TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)) =
      c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 := by
  have hθ : 0 < θ := by linarith
  have hct : 0 < c + t := by linarith
  have hctne : c + t ≠ 0 := hct.ne'
  have hneθ : θ ≠ 0 := hθ.ne'
  have hm0 : (0:ℝ) ≤ c + 2 * t := by positivity
  -- Below the threshold the monopolist output does not exceed t, so the payoff is 0
  have hzero : ∀ x, x ≤ c + 2 * t →
      TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x) = 0 := by
    intro x hx
    have hle : TokenFinance.Debt.qm c x ≤ t := by
      simp only [TokenFinance.Debt.qm]
      exact max_le_iff.mpr ⟨by linarith, ht⟩
    simp only [TokenFinance.Debt.tokEnt]
    rw [if_neg (not_lt.mpr hle)]
  -- Above the threshold the payoff is the exact square (c/(c+t))((x-c)/2 - t)^2
  have hpos : ∀ x, c + 2 * t < x →
      TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
        = c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
    intro x hx
    have hqm : TokenFinance.Debt.qm c x = (x - c) / 2 := by
      simp only [TokenFinance.Debt.qm]
      rw [max_eq_left (by linarith)]
    have hgt : t < TokenFinance.Debt.qm c x := by
      rw [hqm]; linarith
    simp only [TokenFinance.Debt.tokEnt, TokenFinance.Debt.alphaT]
    rw [if_pos hgt, hqm]
    field_simp [hctne]
    ring
  -- unified max-form of the pointwise description
  have hmax : ∀ x, TokenFinance.Debt.tokEnt c t x (TokenFinance.Debt.qm c x)
      = c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2 := by
    intro x
    rcases le_or_gt ((x - c) / 2) t with h | h
    · rw [hzero x (by linarith)]
      rw [show max ((x - (c + 2 * t)) / 2) 0 = 0 from max_eq_right (by linarith)]
      ring
    · rw [hpos x (by linarith)]
      have hident : (x - (c + 2 * t)) / 2 = (x - c) / 2 - t := by ring
      rw [hident, max_eq_left (show 0 ≤ (x - c) / 2 - t from by linarith)]
  have hMcont : Continuous
      (fun x : ℝ => c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) := by fun_prop
  simp only [TokenFinance.Debt.expect]
  rw [intervalIntegral.integral_congr (fun x _ => hmax x)]
  have hsplit :
      (∫ x in (0:ℝ)..θ, c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) =
        (∫ x in (0:ℝ)..(c + 2 * t), c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) +
          (∫ x in (c + 2 * t)..θ, c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hMcont.intervalIntegrable 0 (c + 2 * t)) (hMcont.intervalIntegrable (c + 2 * t) θ)).symm
  have hI1 : ∫ x in (0:ℝ)..(c + 2 * t), c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2 = 0 := by
    have hcong : ∀ x ∈ Set.uIcc (0:ℝ) (c + 2 * t),
        c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2 = 0 := by
      intro x hx
      have hxle : x ≤ c + 2 * t := by
        rw [Set.uIcc_of_le hm0] at hx
        exact (Set.mem_Icc.mp hx).2
      have hzz : max ((x - (c + 2 * t)) / 2) 0 = 0 := max_eq_right (by linarith)
      rw [hzz]
      ring
    rw [intervalIntegral.integral_congr hcong]
    exact intervalIntegral.integral_zero ..
  have hI2 : ∫ x in (c + 2 * t)..θ, c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2
      = c / (c + t) * (2 / 3) * ((θ - c) / 2 - t) ^ 3 := by
    have hcong : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
        c / (c + t) * (max ((x - (c + 2 * t)) / 2) 0) ^ 2
          = c / (c + t) * ((x - c) / 2 - t) ^ 2 := by
      intro x hx
      rw [Set.uIcc_of_le hupper] at hx
      have hxge : c + 2 * t ≤ x := (Set.mem_Icc.mp hx).1
      have hident : (x - (c + 2 * t)) / 2 = (x - c) / 2 - t := by ring
      have hnn : 0 ≤ (x - c) / 2 - t := by linarith
      rw [hident, max_eq_left hnn]
    rw [intervalIntegral.integral_congr hcong]
    have hder : ∀ x ∈ Set.uIcc (c + 2 * t) θ,
        HasDerivAt (fun y : ℝ => c / (c + t) * (2 / 3) * ((y - c) / 2 - t) ^ 3)
          (c / (c + t) * ((x - c) / 2 - t) ^ 2) x := by
      intro x _
      have hb : HasDerivAt (fun y : ℝ => (y - c) / 2 - t) (1 / 2 : ℝ) x := by
        have h := ((hasDerivAt_id' x).sub_const c).div_const 2
        simpa using (h.sub_const t)
      have hmul := (hb.pow 3).const_mul (c / (c + t) * (2 / 3))
      convert hmul using 1 <;> first | rfl | (field_simp [hctne]; ring)
    have hhint : IntervalIntegrable
        (fun x : ℝ => c / (c + t) * ((x - c) / 2 - t) ^ 2) MeasureTheory.volume (c + 2 * t) θ :=
      (show Continuous (fun x : ℝ => c / (c + t) * ((x - c) / 2 - t) ^ 2) by fun_prop).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hhint]
    have hzz : ((c + 2 * t - c) / 2 - t) = 0 := by ring
    rw [hzz]
    ring
  rw [hsplit, hI1, zero_add, hI2]
  field_simp [hneθ, hctne]
