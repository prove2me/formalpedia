-- Prove2me | solution 1 for TokenFinance.OptToken.eq_38_exists
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T21:03:23.256122+00:00
-- url     : https://prove2.me/submissions/330fb124-4ba9-43f7-a601-a9d8447bd4cd

-- MIMO4 solution for TokenFinance.OptToken.eq_38_exists (theorem_id 932ad3b7-6d88-4aa3-be14-1377982f64f8)
-- Existence of an interior break-even size, via the intermediate value theorem.
-- Write G(t) = (c/(c+t))(2/(3 theta))((theta-c)/2 - t)^3, the left side of (16)/(38).
-- By equation (3) (proved inline below by the same interval-integration argument that the
-- platform already verified as TokenFinance.Debt.eq_3), NPV = (theta-c)^3/(12 theta) - C0.
-- Hence G(0) = (theta-c)^3/(12 theta) = NPV + C0 > NPV and G((theta-c)/2) = 0 < NPV, so
-- the continuous function NPV - G changes sign on the interval [0, (theta-c)/2] and
-- vanishes at some t in it. t = 0 would force C0 = 0 and t = (theta-c)/2 would force
-- NPV = 0, both excluded, so 0 < t < (theta-c)/2 and tokenBreakEven holds there.
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θ) :
    ∃ t : ℝ, 0 < t ∧ t < (θ - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θ t := by
  have hθ : 0 < θ := lt_trans hc hcθ
  have hneθ : θ ≠ 0 := hθ.ne'
  have hc0 : c ≠ 0 := ne_of_gt hc
  -- Equation (3): NPV = (theta-c)^3/(12 theta) - C0
  have hcl : TokenFinance.Debt.npv c C0 θ = (θ - c) ^ 3 / (12 * θ) - C0 := by
    have hcθ' : c ≤ θ := hcθ.le
    have hc_pim : Continuous (TokenFinance.Debt.pim c) := by
      unfold TokenFinance.Debt.pim
      fun_prop
    have h_low : ∀ x ∈ Set.uIcc (0 : ℝ) c, TokenFinance.Debt.pim c x = 0 := by
      intro x hx
      have hxc : x ≤ c := by
        rcases Set.mem_uIcc.mp hx with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · linarith [h]
      simp only [TokenFinance.Debt.pim]
      rw [max_eq_right (sub_nonpos_of_le hxc)]
      ring
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
  -- endpoint values of the continuous function NPV - G
  have hmpos : 0 < (θ - c) / 2 := by positivity
  have hG0 : c / (c + 0) * (2 / (3 * θ)) * ((θ - c) / 2 - 0) ^ 3
      = TokenFinance.Debt.npv c C0 θ + C0 := by
    simp only [add_zero, sub_zero]
    rw [hcl]
    simp only [sub_add_cancel]
    field_simp [hneθ, hc0]
    ring
  have hGm : c / (c + (θ - c) / 2) * (2 / (3 * θ)) * ((θ - c) / 2 - (θ - c) / 2) ^ 3 = 0 := by
    simp
  have hcont : ContinuousOn
      (fun t : ℝ => TokenFinance.Debt.npv c C0 θ -
        c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3)
      (Set.Icc 0 ((θ - c) / 2)) := by
    have h1 : ContinuousOn (fun t : ℝ => c / (c + t)) (Set.Icc 0 ((θ - c) / 2)) :=
      continuousOn_const.div (by fun_prop)
        (fun x hx => ne_of_gt (by linarith [hx.1, hc, hmpos]))
    have h2 : ContinuousOn (fun t : ℝ => ((θ - c) / 2 - t) ^ 3) (Set.Icc 0 ((θ - c) / 2)) := by
      fun_prop
    exact continuousOn_const.sub ((h1.mul continuousOn_const).mul h2)
  -- the continuous function NPV - G takes the values -(NPV + C0) + NPV < 0 at t = 0
  -- and NPV > 0 at t = (theta-c)/2
  have hmem : (0:ℝ) ∈ Set.Icc
      ((fun t : ℝ => TokenFinance.Debt.npv c C0 θ -
        c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3) 0)
      ((fun t : ℝ => TokenFinance.Debt.npv c C0 θ -
        c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3) ((θ - c) / 2)) := by
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · show TokenFinance.Debt.npv c C0 θ -
        c / (c + 0) * (2 / (3 * θ)) * ((θ - c) / 2 - 0) ^ 3 ≤ 0
      rw [hG0]
      linarith
    · show 0 ≤ TokenFinance.Debt.npv c C0 θ -
        c / (c + (θ - c) / 2) * (2 / (3 * θ)) * ((θ - c) / 2 - (θ - c) / 2) ^ 3
      rw [hGm]
      linarith
  have hiv := intermediate_value_Icc (le_of_lt hmpos) hcont
  obtain ⟨t, htmem, hteq⟩ := hiv hmem
  have ht : TokenFinance.Debt.npv c C0 θ -
      c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 = 0 := hteq
  have ht0 : 0 < t := by
    rcases htmem with ⟨hle, _⟩
    rcases eq_or_lt_of_le hle with h | h
    · subst h
      rw [hG0] at ht
      linarith
    · exact h
  have htm : t < (θ - c) / 2 := by
    rcases htmem with ⟨_, hge⟩
    rcases eq_or_lt_of_le hge with h | h
    · subst h
      rw [hGm] at ht
      linarith
    · exact h
  refine ⟨t, ht0, htm, ?_⟩
  rw [TokenFinance.Debt.tokenBreakEven]
  exact (eq_of_sub_eq_zero ht).symm.trans hcl
