-- Prove2me | solution 1 for TokenFinance.OptToken.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:27:11.028214+00:00
-- url     : https://prove2.me/submissions/c8748dce-4f06-4a2d-a8a8-b83109ef0ac8

-- MIMO3 solution for TokenFinance.OptToken.eq_3 (theorem_id e3b5ca3b-d637-4d26-9d25-b538fa0c58e9)
-- Same statement as the accepted TokenFinance.Debt.eq_3 (7815d422): the OptToken milestone
-- re-states equation (3), so the previously verified integration proof is reused verbatim.
-- Target: npv c C0 θ = (θ - c)^3 / (12 * θ) - C0, for 0 < c < θ.
-- NPV = (∫_0^θ π^m(x) dx)/θ - C0 with π^m(x) = (max (x-c) 0)^2 / 4.
-- π^m vanishes on [0,c]; on [c,θ] it equals (x-c)^2/4, whose antiderivative is
-- (x-c)^3/12, so ∫_0^θ π^m = (θ-c)^3/12.
import Definitions.Def_TokenFinance_Debt_Setting

open TokenFinance.Debt

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) :
    TokenFinance.Debt.npv c C0 θ = (θ - c) ^ 3 / (12 * θ) - C0 := by
  have hθ : 0 < θ := lt_trans hc hcθ
  have hcθ' : c ≤ θ := hcθ.le
  have hc_pim : Continuous (TokenFinance.Debt.pim c) := by
    unfold TokenFinance.Debt.pim
    fun_prop
  -- π^m vanishes on [0, c]
  have h_low : ∀ x ∈ Set.uIcc (0 : ℝ) c, TokenFinance.Debt.pim c x = 0 := by
    intro x hx
    have hxc : x ≤ c := by
      rcases Set.mem_uIcc.mp hx with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · linarith [h]
    simp only [TokenFinance.Debt.pim]
    rw [max_eq_right (sub_nonpos_of_le hxc)]
    ring
  -- π^m coincides with (x-c)^2/4 on [c, θ]
  have h_mid : ∀ x ∈ Set.uIcc c θ, TokenFinance.Debt.pim c x = (x - c) ^ 2 / 4 := by
    intro x hx
    have hcx : c ≤ x := by
      rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · linarith [h, hcθ']
    simp only [TokenFinance.Debt.pim]
    rw [max_eq_left (sub_nonneg_of_le hcx)]
  have hI_low : ∫ x in (0 : ℝ)..c, TokenFinance.Debt.pim c x = 0 := by
    rw [intervalIntegral.integral_congr (fun x hx => h_low x hx)]
    exact intervalIntegral.integral_zero ..
  have hI_mid : ∫ x in c..θ, TokenFinance.Debt.pim c x = (θ - c) ^ 3 / 12 := by
    rw [intervalIntegral.integral_congr (fun x hx => h_mid x hx)]
    have hint : IntervalIntegrable (fun x : ℝ => (x - c) ^ 2 / 4) MeasureTheory.volume c θ :=
      (show Continuous (fun x : ℝ => (x - c) ^ 2 / 4) by fun_prop).intervalIntegrable c θ
    have hderiv : ∀ x ∈ Set.uIcc c θ,
        HasDerivAt (fun y : ℝ => (y - c) ^ 3 / 12) ((x - c) ^ 2 / 4) x := by
      intro x _
      have h3 := (((hasDerivAt_id' x).sub_const c).pow 3).div_const 12
      simp at h3
      convert h3 using 1 <;> first | rfl | (field_simp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  have h_split : ∫ x in (0 : ℝ)..θ, TokenFinance.Debt.pim c x
      = (∫ x in (0 : ℝ)..c, TokenFinance.Debt.pim c x) + ∫ x in c..θ, TokenFinance.Debt.pim c x :=
    (intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc_pim.intervalIntegrable 0 c) (hc_pim.intervalIntegrable c θ)).symm
  simp only [TokenFinance.Debt.npv, TokenFinance.Debt.expect]
  rw [h_split, hI_low, hI_mid, zero_add, div_div]
