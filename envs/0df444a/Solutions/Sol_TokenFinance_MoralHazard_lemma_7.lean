-- Prove2me | solution 1 for TokenFinance.MoralHazard.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T12:10:45.321986+00:00
-- url     : https://prove2.me/submissions/3b062449-1245-4708-81a0-c53b73221187

/-
DS19E proof of the MoralHazard milestone TokenFinance.MoralHazard.lemma_7
(theorem_id a8ae7ddb-97b9-4f0b-b6b9-2f46c1f2ff36), Lemma 7 (31).

Mathematics.  As in lemma_6, with L = θh − c, δ = 2√D/L, τ = 2t/L, the accepted
milestones (48) and (3) give C₀ = L³/(12θh)(3δ² − 2δ³), and the token break-even
equation becomes
  c/(c+t)·(1−τ)³ = (1−δ)²(1+2δ).      (∗)
The same argument as in lemma_6 yields 0 < τ < δ² < δ < 1; in particular τ < λ
because δ < λ.

First inequality: λ(1−τ) − (λ−τ) = τ(1−λ) > 0, and both sides are positive, so
λ³(1−τ)³ > (λ−τ)³, i.e. λ³ > (λ−τ)³/(1−τ)³.

Second inequality: f(u) = ((λ−u)/(1−u))³ is strictly decreasing on [0,1) because
(λ−u)(1−v) − (λ−v)(1−u) = (v−u)(1−λ) > 0 for u < v.  With τ < δ² this gives
f(τ) > f(δ²).  Finally f(δ²) > g(δ), where g(δ) = (λ−δ)²(λ+2δ)/((1−δ)²(1+2δ)):
the difference equals
  δ²(1−λ)·B / ((1−δ)³(1+δ)³(1+2δ)),
with B = δ(1−δ)²(1+2δ) + (λ−δ)(1−δ)(δ²+5δ+3) + δ(2+δ)(λ−δ)(1−λ) > 0
for 0 < δ < λ < 1.  (The middle coefficient uses
3+2δ−4δ²−δ³ = (1−δ)(δ²+5δ+3).)  All factors are positive, hence f(δ²) > g(δ).
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Theorems.Thm_TokenFinance_Debt_eq_3
import Theorems.Thm_TokenFinance_MoralHazard_eq_48

set_option maxHeartbeats 800000 in
theorem solution (c C0 θh D t δ τ lam : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) (hD : 0 ≤ D) (hBE : TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0)
    (ht0 : 0 < t) (ht1 : t < (θh - c) / 2) (hT : TokenFinance.Debt.tokenBreakEven c C0 θh t)
    (hδ : δ = 2 * Real.sqrt D / (θh - c)) (hτ : τ = 2 * t / (θh - c))
    (hδl : δ < lam) (hl1 : lam < 1) :
    lam ^ 3 > (lam - τ) ^ 3 / (1 - τ) ^ 3 ∧
      (lam - τ) ^ 3 / (1 - τ) ^ 3 >
        (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) := by
  have hθh : 0 < θh := lt_trans hc hcθ
  have hθhne : θh ≠ 0 := ne_of_gt hθh
  have hL : 0 < θh - c := by linarith
  have hLne : θh - c ≠ 0 := ne_of_gt hL
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (by positivity) hL.le
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
  have hδ2lt : δ ^ 2 < δ := by nlinarith [hδpos, hδ1]
  have hτlam : τ < lam := by linarith
  have hlampos : 0 < lam := by linarith
  constructor
  · -- first inequality: λ³ > (λ−τ)³/(1−τ)³
    have hlt : lam - τ < lam * (1 - τ) := by nlinarith only [hτpos, hl1]
    have h0 : 0 ≤ lam - τ := by linarith
    have hcube : (lam - τ) ^ 3 < (lam * (1 - τ)) ^ 3 :=
      pow_lt_pow_left₀ hlt h0 (by norm_num : (3 : ℕ) ≠ 0)
    rw [mul_pow] at hcube
    have hq : (lam - τ) ^ 3 / (1 - τ) ^ 3 < lam ^ 3 := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (1 - τ) ^ 3)]
      linarith [hcube]
    linarith [hq]
  · -- second inequality
    have hff : (lam - δ ^ 2) ^ 3 / (1 - δ ^ 2) ^ 3 <
        (lam - τ) ^ 3 / (1 - τ) ^ 3 := by
      have hnum0 : 0 ≤ lam - δ ^ 2 := by linarith
      have hden0 : 0 < 1 - δ ^ 2 := by
        have h1d : 0 < 1 - δ := by linarith
        have hh : 0 < (1 - δ) * (1 + δ) := mul_pos h1d (by linarith)
        rwa [show 1 - δ ^ 2 = (1 - δ) * (1 + δ) by ring]
      have hcross : (lam - δ ^ 2) * (1 - τ) < (lam - τ) * (1 - δ ^ 2) := by
        nlinarith only [hτδ2, hl1]
      have hdiv : (lam - δ ^ 2) / (1 - δ ^ 2) < (lam - τ) / (1 - τ) := by
        rw [div_lt_div_iff₀ hden0 (show (0 : ℝ) < 1 - τ by linarith)]
        exact hcross
      have hnn : 0 ≤ (lam - δ ^ 2) / (1 - δ ^ 2) := div_nonneg hnum0 hden0.le
      have hpow := pow_lt_pow_left₀ hdiv hnn (by norm_num : (3 : ℕ) ≠ 0)
      rwa [div_pow, div_pow] at hpow
    have hfmid : (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) <
        (lam - δ ^ 2) ^ 3 / (1 - δ ^ 2) ^ 3 := by
      set B : ℝ := δ * (1 - δ) ^ 2 * (1 + 2 * δ) + (lam - δ) * (1 - δ) * (δ ^ 2 + 5 * δ + 3)
        + δ * (2 + δ) * (lam - δ) * (1 - lam) with hBdef
      have h1d : 0 < 1 - δ := by linarith
      have h1p : 0 < 1 + δ := by linarith
      have h12 : 0 < 1 + 2 * δ := by linarith
      have hquad : 0 < δ ^ 2 + 5 * δ + 3 := by nlinarith only [hδpos]
      have hB : 0 < B := by
        rw [hBdef]
        have hterm1 : 0 < δ * (1 - δ) ^ 2 * (1 + 2 * δ) :=
          mul_pos (mul_pos hδpos (pow_pos h1d 2)) h12
        have hterm2 : 0 < (lam - δ) * (1 - δ) * (δ ^ 2 + 5 * δ + 3) :=
          mul_pos (mul_pos (by linarith) h1d) hquad
        have hterm3 : 0 < δ * (2 + δ) * (lam - δ) * (1 - lam) :=
          mul_pos (mul_pos (mul_pos hδpos (by linarith)) (by linarith)) (by linarith)
        linarith [hterm1, hterm2, hterm3]
      -- the cross-multiplied numerator identity
      have hN : (lam - δ ^ 2) ^ 3 * ((1 - δ) ^ 2 * (1 + 2 * δ)) -
          (lam - δ) ^ 2 * (lam + 2 * δ) * ((1 - δ ^ 2) ^ 3) =
          δ ^ 2 * (1 - lam) * B * (1 - δ) ^ 2 := by
        rw [hBdef]
        ring
      have hNpos : 0 < (lam - δ ^ 2) ^ 3 * ((1 - δ) ^ 2 * (1 + 2 * δ)) -
          (lam - δ) ^ 2 * (lam + 2 * δ) * ((1 - δ ^ 2) ^ 3) := by
        rw [hN]
        exact mul_pos (mul_pos (mul_pos (pow_pos hδpos 2) (by linarith)) hB) (pow_pos h1d 2)
      have hdg : 0 < (1 - δ) ^ 2 * (1 + 2 * δ) := mul_pos (pow_pos h1d 2) h12
      have hdf : 0 < (1 - δ ^ 2) ^ 3 := by
        have hh : 0 < (1 - δ) * (1 + δ) := mul_pos h1d h1p
        rw [show (1 - δ ^ 2) = (1 - δ) * (1 + δ) by ring]
        exact pow_pos hh 3
      have hgeq : (lam - δ) ^ 2 / (1 - δ) ^ 2 * ((lam + 2 * δ) / (1 + 2 * δ)) =
          (lam - δ) ^ 2 * (lam + 2 * δ) / ((1 - δ) ^ 2 * (1 + 2 * δ)) := by
        rw [div_mul_div_comm]
      rw [hgeq, div_lt_div_iff₀ hdg hdf]
      linarith [hNpos]
    exact lt_trans hfmid hff
