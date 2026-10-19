-- Prove2me | solution 1 for TokenFinance.MoralHazard.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T12:10:38.124474+00:00
-- url     : https://prove2.me/submissions/38a52c50-0a20-4e10-b1a3-e633f589baed

/-
DS19E proof of the MoralHazard milestone TokenFinance.MoralHazard.lemma_6
(theorem_id 36e7e210-3fc9-4916-8489-de658f56ab33), Lemma 6 / Appendix A (57).

Mathematics.  Write L = θh − c > 0, δ = 2√D/L and τ = 2t/L.  From the accepted
platform milestone eq_48 (48) and eq_3 (3) we obtain, purely algebraically,
  C₀ = L³/(12θh)·(3δ² − 2δ³) = L³/(12θh)·(1 − (1−δ)²(1+2δ)).
The token break-even equation (38) then becomes
  c/(c+t)·(1−τ)³ = (1−δ)²(1+2δ).      (∗)
Indeed (2/(3θh))((L/2−t)³) = L³/(12θh)(1−τ)³.

First δ < 1.  If D ≥ L²/4 then min(π^m,D) = π^m everywhere on (0,θh), so
C₀ = E[π^m] = L³/(12θh) (by (3)) and NPV_h = E[π^m] − C₀ = 0, contradicting
NPV_h > 0.  Hence D < L²/4 and δ = 2√D/L < 1.  Since C₀ > 0, (3δ²−2δ³) > 0,
and as 3−2δ > 0 this gives δ > 0.

Finally τ < δ².  Suppose δ² ≤ τ.  Since 0 ≤ τ < 1,
(1−τ)³ ≤ (1−δ²)³, and 0 < c/(c+t) ≤ 1, so the left side of (∗) is at most
(1−δ²)³.  But
  (1−δ)²(1+2δ) − (1−δ²)³ = δ³(1−δ)²(δ+2) > 0,
so the left side of (∗) is strictly smaller than its right side, contradiction.
Thus τ < δ², and δ² < δ follows from 0 < δ < 1.  All four claims follow.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Theorems.Thm_TokenFinance_Debt_eq_3
import Theorems.Thm_TokenFinance_MoralHazard_eq_48

theorem solution (c C0 θh D t δ τ : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (ht0 : 0 < t) (ht1 : t < (θh - c) / 2) (hT : TokenFinance.Debt.tokenBreakEven c C0 θh t)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) (hτ : τ = 2 * t / (θh - c)) :
    0 < τ ∧ τ < δ ^ 2 ∧ δ ^ 2 < δ ∧ δ < 1 := by
  have hθh : 0 < θh := lt_trans hc hcθ
  have hθhne : θh ≠ 0 := ne_of_gt hθh
  have hL : 0 < θh - c := by linarith
  have hLne : θh - c ≠ 0 := ne_of_gt hL
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (by positivity) hL.le
  -- D < L^2/4, otherwise debt pays pi^m everywhere and the NPV vanishes
  have hDlt : D < (θh - c) ^ 2 / 4 := by
    by_contra hcon
    have hge : (θh - c) ^ 2 / 4 ≤ D := le_of_not_gt hcon
    have hpoint : ∀ x ∈ Set.uIcc (0 : ℝ) θh,
        TokenFinance.Debt.debtInv c D x = TokenFinance.Debt.pim c x := by
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt hθh)] at hx
      have hxle : x ≤ θh := hx.2
      have hpimle : TokenFinance.Debt.pim c x ≤ (θh - c) ^ 2 / 4 := by
        unfold TokenFinance.Debt.pim
        have h1 : max (x - c) 0 ≤ θh - c := max_le (by linarith) hL.le
        have h0 : 0 ≤ max (x - c) 0 := le_max_right _ _
        nlinarith [sq_nonneg (max (x - c) 0)]
      unfold TokenFinance.Debt.debtInv
      exact min_eq_left (le_trans hpimle hge)
    have hCE : C0 = TokenFinance.Debt.expect θh (TokenFinance.Debt.pim c) := by
      rw [← hBE]
      unfold TokenFinance.Debt.expect
      rw [intervalIntegral.integral_congr hpoint]
    have hnpv0 : TokenFinance.Debt.npv c C0 θh = 0 := by
      unfold TokenFinance.Debt.npv
      linarith
    linarith
  have hsqrt_lt : Real.sqrt D < (θh - c) / 2 := by
    rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < (θh - c) / 2)]
    nlinarith
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one hL]
    nlinarith
  -- the closed form for C0 from the accepted milestones (48) and (3)
  have h48 := TokenFinance.MoralHazard.eq_48 c C0 θh D δ hc hcθ hC0 hnpv hD hBE hδ
  have h3 := TokenFinance.Debt.eq_3 c C0 θh hc hcθ
  have hC0eq : C0 = (θh - c) ^ 3 / (12 * θh) * (3 * δ ^ 2 - 2 * δ ^ 3) := by
    have hlin : C0 = (θh - c) ^ 3 / (12 * θh) -
        (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := by
      linarith [h3, h48.2]
    calc C0 = (θh - c) ^ 3 / (12 * θh) -
          (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := hlin
      _ = (θh - c) ^ 3 / (12 * θh) * (3 * δ ^ 2 - 2 * δ ^ 3) := by ring
  have hApos : 0 < (θh - c) ^ 3 / (12 * θh) := by positivity
  have hX : 0 < 3 * δ ^ 2 - 2 * δ ^ 3 := by
    have hAne : (θh - c) ^ 3 / (12 * θh) ≠ 0 := ne_of_gt hApos
    have hquot : C0 / ((θh - c) ^ 3 / (12 * θh)) = 3 * δ ^ 2 - 2 * δ ^ 3 := by
      field_simp [hAne] at hC0eq ⊢
      linarith [hC0eq]
    rw [← hquot]
    positivity
  have hfac : 0 < δ ^ 2 * (3 - 2 * δ) := by nlinarith [hX]
  have hδne : δ ≠ 0 := by
    intro h0
    rw [h0] at hfac
    norm_num at hfac
  have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδne)
  have hτpos : 0 < τ := by
    rw [hτ]
    exact div_pos (by positivity) hL
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one hL]
    nlinarith
  -- the token break-even equation in normalised form
  have hident : (2 / (3 * θh)) * (((θh - c) / 2 - t) ^ 3) =
      (θh - c) ^ 3 / (12 * θh) * (1 - τ) ^ 3 := by
    rw [hτ]
    field_simp [hθhne, hLne]
    ring
  have hT2 : c / (c + t) * ((θh - c) ^ 3 / (12 * θh) * (1 - τ) ^ 3) =
      (θh - c) ^ 3 / (12 * θh) - C0 := by
    rw [← hident]
    simpa [TokenFinance.Debt.tokenBreakEven, mul_assoc] using hT
  have hR : (θh - c) ^ 3 / (12 * θh) - C0 =
      (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := by
    rw [hC0eq]
    ring
  have hT3 : c / (c + t) * ((θh - c) ^ 3 / (12 * θh) * (1 - τ) ^ 3) =
      (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := by
    rw [← hR]
    exact hT2
  have hrel : c / (c + t) * (1 - τ) ^ 3 = (1 - δ) ^ 2 * (1 + 2 * δ) := by
    have hAne : (θh - c) ^ 3 / (12 * θh) ≠ 0 := ne_of_gt hApos
    refine mul_left_cancel₀ hAne ?_
    calc (θh - c) ^ 3 / (12 * θh) * (c / (c + t) * (1 - τ) ^ 3)
        = c / (c + t) * ((θh - c) ^ 3 / (12 * θh) * (1 - τ) ^ 3) := by ring
      _ = (θh - c) ^ 3 / (12 * θh) * (1 - 3 * δ ^ 2 + 2 * δ ^ 3) := hT3
      _ = (θh - c) ^ 3 / (12 * θh) * ((1 - δ) ^ 2 * (1 + 2 * δ)) := by ring
  -- tau < delta^2 by comparison with the value at delta^2
  have hτδ2 : τ < δ ^ 2 := by
    by_contra hcon
    have hge : δ ^ 2 ≤ τ := le_of_not_gt hcon
    have h1 : (1 - τ) ^ 3 ≤ (1 - δ ^ 2) ^ 3 := by
      have hle : 1 - τ ≤ 1 - δ ^ 2 := by linarith
      have h0 : 0 ≤ 1 - τ := by linarith
      exact pow_le_pow_left₀ h0 hle 3
    have h2 : c / (c + t) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < c + t)]
      linarith
    have h3 : (1 - δ ^ 2) ^ 3 < (1 - δ) ^ 2 * (1 + 2 * δ) := by
      have hdiff : (1 - δ) ^ 2 * (1 + 2 * δ) - (1 - δ ^ 2) ^ 3 =
          δ ^ 3 * (1 - δ) ^ 2 * (δ + 2) := by ring
      have h1d : 0 < 1 - δ := by linarith
      have hd2 : 0 < δ + 2 := by linarith
      have hpos : 0 < δ ^ 3 * (1 - δ) ^ 2 * (δ + 2) :=
        mul_pos (mul_pos (pow_pos hδpos 3) (pow_pos h1d 2)) hd2
      linarith [hdiff, hpos]
    have hle1 : 0 ≤ (1 - τ) ^ 3 := by positivity
    have hle2 : 0 ≤ c / (c + t) := by positivity
    have hprod : c / (c + t) * (1 - τ) ^ 3 ≤ (1 - δ ^ 2) ^ 3 := by
      have := mul_le_mul h2 h1 hle1 zero_le_one
      simpa using this
    linarith
  exact ⟨hτpos, hτδ2, by nlinarith [hδpos, hδ1], hδ1⟩
