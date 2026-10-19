-- Prove2me | solution 1 for TokenFinance.OptToken.eq_39_40
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:27:12.076271+00:00
-- url     : https://prove2.me/submissions/3d85f155-7228-41ae-8cfb-58e59e290d07

-- MIMO3 solution for TokenFinance.OptToken.eq_39_40 (theorem_id cf36aea1-a290-4e4f-a933-caa60fb120c6)
-- Equations (39)-(40), Malinova & Park. Let f = rootPolynomial (the cubic (39)).
-- Strictness, purely algebraically: for a < b,
--   f(b) - f(a) = (b-a) * [ ((a+b)/2 - (θ-c)/2)^2 + (a-b)^2/12 + θ·NPV/(2c) ],
-- (completing the square for the quadratic quotient of the cubic difference; the
-- constant (θ-c)²/4 of f cancels against ((θ-c)/2)²). Every bracket term is ≥ 0 and
-- θ·NPV/(2c) > 0 since 0 < c < θ and NPV > 0, so f(b) - f(a) > 0 whenever a < b.
-- Break-even (16) ⟺ f(t) = 0 for t > -c: writing N = (θ-c)³/(12θ) - C0 (= NPV by the
-- closed form of (3), proved inline below), one checks the single rational identity
--   2c·f(t) = -θ(c+t)·[ (c/(c+t))(2/(3θ))((θ-c)/2-t)³ - N ],
-- whose bracket is exactly LHS−RHS of (16); the multipliers 2c and -θ(c+t) are
-- nonzero for t > -c, so the two vanish simultaneously — this is (39)-(38).
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_OptToken_RootPolynomial

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θ) :
    StrictMono (TokenFinance.OptToken.rootPolynomial c C0 θ) ∧
      ∀ t : ℝ, -c < t →
        (TokenFinance.Debt.tokenBreakEven c C0 θ t ↔
          TokenFinance.OptToken.rootPolynomial c C0 θ t = 0) := by
  have hθ : 0 < θ := lt_trans hc hcθ
  have hc0 : c ≠ 0 := ne_of_gt hc
  have ht0 : θ ≠ 0 := ne_of_gt hθ
  -- NPV closed form (3): the integration argument previously accepted as TokenFinance.Debt.eq_3
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
        rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩
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
  refine ⟨fun a b hab => ?_, fun t htc => ?_⟩
  · -- StrictMono: the cubic difference factors as (b-a) times a manifestly positive bracket
    have key : TokenFinance.OptToken.rootPolynomial c C0 θ b -
        TokenFinance.OptToken.rootPolynomial c C0 θ a =
        (b - a) * (((a + b) / 2 - (θ - c) / 2) ^ 2 + (a - b) ^ 2 / 12 +
          θ / (2 * c) * TokenFinance.Debt.npv c C0 θ) := by
      simp only [TokenFinance.OptToken.rootPolynomial]
      ring
    have hpos : 0 < ((a + b) / 2 - (θ - c) / 2) ^ 2 + (a - b) ^ 2 / 12 +
        θ / (2 * c) * TokenFinance.Debt.npv c C0 θ := by
      have h1 : 0 ≤ ((a + b) / 2 - (θ - c) / 2) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (a - b) ^ 2 / 12 := by positivity
      have h3 : 0 < θ / (2 * c) * TokenFinance.Debt.npv c C0 θ :=
        mul_pos (div_pos hθ (by linarith)) hnpv
      linarith
    have hprod : 0 < (b - a) * (((a + b) / 2 - (θ - c) / 2) ^ 2 + (a - b) ^ 2 / 12 +
        θ / (2 * c) * TokenFinance.Debt.npv c C0 θ) := mul_pos (sub_pos_of_lt hab) hpos
    linarith [key, hprod]
  · -- break-even (16) iff the cubic vanishes
    have hct : 0 < c + t := by linarith
    have hctne : c + t ≠ 0 := hct.ne'
    have h2c : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc0
    have hnz : -θ * (c + t) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ht0) hctne
    -- the single rational bridge between (16) and the cubic
    have ident :
        2 * c * (t ^ 3 / 3 - t ^ 2 * ((θ - c) / 2) +
            t * ((θ - c) ^ 2 / 4 + θ / (2 * c) * ((θ - c) ^ 3 / (12 * θ) - C0)) - θ / 2 * C0) =
          -θ * (c + t) * (c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
            ((θ - c) ^ 3 / (12 * θ) - C0)) := by
      field_simp [ht0, hc0, hctne]
      ring
    constructor
    · intro h
      rw [TokenFinance.Debt.tokenBreakEven] at h
      simp only [TokenFinance.OptToken.rootPolynomial]
      rw [hcl]
      have hdz : c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
          ((θ - c) ^ 3 / (12 * θ) - C0) = 0 := sub_eq_zero.mpr h
      have hz : 2 * c * (t ^ 3 / 3 - t ^ 2 * ((θ - c) / 2) +
          t * ((θ - c) ^ 2 / 4 + θ / (2 * c) * ((θ - c) ^ 3 / (12 * θ) - C0)) - θ / 2 * C0) = 0 := by
        rw [ident, hdz, mul_zero]
      exact (mul_eq_zero.mp hz).resolve_left h2c
    · intro h
      rw [TokenFinance.Debt.tokenBreakEven]
      simp only [TokenFinance.OptToken.rootPolynomial] at h
      rw [hcl] at h
      rw [h] at ident
      rw [mul_zero] at ident
      have hdz : c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 -
          ((θ - c) ^ 3 / (12 * θ) - C0) = 0 :=
        (mul_eq_zero.mp ident.symm).resolve_left hnz
      exact sub_eq_zero.mp hdz
