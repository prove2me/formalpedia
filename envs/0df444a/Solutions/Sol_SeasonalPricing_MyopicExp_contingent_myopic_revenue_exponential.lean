-- Prove2me | solution 1 for SeasonalPricing.MyopicExp.contingent_myopic_revenue_exponential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T05:12:55.349362+00:00
-- url     : https://prove2.me/submissions/a9734ee6-2632-4089-a7bd-a458eb6c8880

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicExp_gammaValuationTail
import Definitions.Def_SeasonalPricing_Shared_LambdaI
import Definitions.Def_SeasonalPricing_MyopicExp_contingentMyopicRevenue

set_option autoImplicit false

open SeasonalPricing.MyopicExp SeasonalPricing.Shared in
theorem solution (lam α T : ℝ) (hlam : 0 < lam) (hT0 : 0 < T)
    (hT1 : T ≤ 1) (hα : 0 ≤ α) (hρ : decayRatio α 1 = 1) :
    IsGreatest {r : ℝ | ∃ p1 p2 : ℝ, p2 ≤ p1 ∧
        r = contingentMyopicRevenue lam α T 1 (gammaValuationTail 1 1) p1 p2}
      (lam * Real.exp (-1) * Real.exp (T / Real.exp 1)) ∧
    IsGreatest {r : ℝ | ∃ p : ℝ, r = fixedPriceRevenue lam α 1 (gammaValuationTail 1 1) p}
      (lam * Real.exp (-1)) := by
  -- ρ = 1 forces α = 0
  have hα0 : α = 0 := by
    unfold decayRatio at hρ
    have h := (Real.exp_eq_one_iff _).mp hρ
    linarith [mul_one α]
  subst hα0
  -- closed form of the exponential tail
  have hF : ∀ x : ℝ, gammaValuationTail 1 1 x = if 0 ≤ x then Real.exp (-x) else 1 := by
    intro x
    have h := ProbabilityTheory.cdf_expMeasure_eq (r := 1) one_pos x
    unfold ProbabilityTheory.expMeasure at h
    unfold gammaValuationTail
    simp only [one_pow, div_one, mul_one, one_mul] at h ⊢
    rw [h]
    split_ifs <;> ring
  have hFpos : ∀ x : ℝ, 0 ≤ x → gammaValuationTail 1 1 x = Real.exp (-x) := by
    intro x hx; rw [hF, if_pos hx]
  have hFneg : ∀ x : ℝ, x < 0 → gammaValuationTail 1 1 x = 1 := by
    intro x hx; rw [hF, if_neg (not_le.mpr hx)]
  -- closed forms of the two revenues
  have hrev : ∀ p1 p2 : ℝ, p2 ≤ p1 →
      contingentMyopicRevenue lam 0 T 1 (gammaValuationTail 1 1) p1 p2
        = lam * (T * gammaValuationTail 1 1 p1 * (p1 - p2)
            + p2 * gammaValuationTail 1 1 p2) := by
    intro p1 p2 h
    simp only [contingentMyopicRevenue, LambdaI, LambdaW, LambdaL, zero_mul, Real.exp_zero,
      mul_one, min_eq_right h, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hfix : ∀ p : ℝ, fixedPriceRevenue lam 0 1 (gammaValuationTail 1 1) p
      = lam * (p * gammaValuationTail 1 1 p) := by
    intro p
    simp only [fixedPriceRevenue, zero_mul, Real.exp_zero, mul_one,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  -- the one-variable bound x e^{-x} ≤ e^{-1}
  have key : ∀ x : ℝ, x * Real.exp (-x) ≤ Real.exp (-1) := by
    intro x
    have h1 : x - 1 + 1 ≤ Real.exp (x - 1) := Real.add_one_le_exp _
    have h2 : 0 < Real.exp (-x) := Real.exp_pos _
    have h3 : Real.exp (x - 1) * Real.exp (-x) = Real.exp (-1) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = T / Real.exp 1 := ⟨_, rfl⟩
  rw [← hs]
  have he1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hTs : T = s * Real.exp 1 := by rw [hs]; field_simp
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by
    rw [hs]
    exact le_trans (div_le_self hT0.le (Real.one_le_exp zero_le_one)) hT1
  have hsT : T * Real.exp (-1) = s := by
    rw [hTs, mul_assoc, ← Real.exp_add]; norm_num
  have hes : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have hem : 0 < Real.exp (-1) := Real.exp_pos _
  refine ⟨⟨⟨2 - s, 1 - s, by linarith, ?_⟩, ?_⟩, ⟨⟨1, ?_⟩, ?_⟩⟩
  · -- attainment of the contingent optimum
    rw [hrev _ _ (by linarith), hFpos _ (by linarith), hFpos _ (by linarith)]
    have h1 : Real.exp (-(2 - s)) * Real.exp 1 = Real.exp (-(1 - s)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(1 - s)) = Real.exp (-1) * Real.exp s := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (-lam * Real.exp (-(2 - s))) * hTs + (-lam * s) * h1 + (-lam) * h2
  · -- upper bound for the contingent revenue
    rintro r ⟨p1, p2, hp, rfl⟩
    rw [hrev _ _ hp]
    suffices hin : T * gammaValuationTail 1 1 p1 * (p1 - p2) + p2 * gammaValuationTail 1 1 p2
        ≤ Real.exp (-1) * Real.exp s by
      calc lam * (T * gammaValuationTail 1 1 p1 * (p1 - p2) + p2 * gammaValuationTail 1 1 p2)
          ≤ lam * (Real.exp (-1) * Real.exp s) := mul_le_mul_of_nonneg_left hin hlam.le
        _ = lam * Real.exp (-1) * Real.exp s := by ring
    rcases le_or_gt 0 p2 with h2 | h2
    · have h1 : 0 ≤ p1 := le_trans h2 hp
      rw [hFpos _ h1, hFpos _ h2]
      have hu := key (p1 - p2)
      have hv := key (s + p2)
      have e1 : Real.exp (-p1) = Real.exp (-(p1 - p2)) * Real.exp (-p2) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp (-p2) = Real.exp s * Real.exp (-(s + p2)) := by
        rw [← Real.exp_add]; ring_nf
      have hp2 : 0 < Real.exp (-p2) := Real.exp_pos _
      calc T * Real.exp (-p1) * (p1 - p2) + p2 * Real.exp (-p2)
          = Real.exp (-p2) * (T * ((p1 - p2) * Real.exp (-(p1 - p2))) + p2) := by
            rw [e1]; ring
        _ ≤ Real.exp (-p2) * (T * Real.exp (-1) + p2) := by
            apply mul_le_mul_of_nonneg_left _ hp2.le
            have := mul_le_mul_of_nonneg_left hu hT0.le
            linarith
        _ = Real.exp s * ((s + p2) * Real.exp (-(s + p2))) := by
            rw [hsT, e2]; ring
        _ ≤ Real.exp s * Real.exp (-1) := mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
        _ = Real.exp (-1) * Real.exp s := by ring
    · rw [hFneg _ h2]
      rcases le_or_gt 0 p1 with h1 | h1
      · rw [hFpos _ h1]
        have a1 := key p1
        have a2 : Real.exp (-p1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have b1 := mul_le_mul_of_nonneg_left a1 hT0.le
        have b2 := mul_le_mul_of_nonneg_left a2 (mul_nonneg hT0.le (by linarith : (0:ℝ) ≤ -p2))
        have b3 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - T) (by linarith : (0:ℝ) ≤ -p2)
        have b4 := mul_le_mul_of_nonneg_right hT1 hem.le
        have b5 := mul_le_mul_of_nonneg_left hes hem.le
        nlinarith
      · rw [hFneg _ h1]
        have b3 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - T) (by linarith : (0:ℝ) ≤ -p2)
        have b6 : 0 < Real.exp (-1) * Real.exp s := by positivity
        nlinarith
  · -- attainment of the fixed-price optimum
    rw [hfix, hFpos _ zero_le_one]
    ring
  · -- upper bound for the fixed-price revenue
    rintro r ⟨p, rfl⟩
    rw [hfix]
    apply mul_le_mul_of_nonneg_left _ hlam.le
    rcases le_or_gt 0 p with hp | hp
    · rw [hFpos _ hp]; exact key p
    · rw [hFneg _ hp]; linarith
