-- Prove2me | solution 1 for ShockWear.Inherit.Supplement.theorem32_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:19.204802+00:00
-- url     : https://prove2.me/submissions/d81cb538-be34-4a9a-a254-d5b273baeb7b

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
import Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing

open ShockWear
open ShockWear.Inherit
open ShockWear.Inherit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k →
      P j ^ (1 / (j : ℝ)) ≤ P k ^ (1 / (k : ℝ))) :
    IsDHRA (ShockWear.CumDamage.shockSurv lam P) := by
      intro s hs t ht hst
      simp only [Set.mem_Ioi] at hs ht
      have hP1 : ∀ k, P k ≤ 1 := fun k => (hanti (Nat.zero_le k)).trans hP0
      have hsum : ∀ z : ℝ, 0 ≤ z → Summable (fun k : ℕ => P k * z ^ k / (k.factorial : ℝ)) := by
        intro z hz
        refine Summable.of_nonneg_of_le
          (fun k => div_nonneg (mul_nonneg (hnn k) (pow_nonneg hz k)) (by positivity))
          (fun k => ?_) (Real.summable_pow_div_factorial z)
        rw [mul_div_assoc]
        exact mul_le_of_le_one_left (by positivity) (hP1 k)
      set G : ℝ → ℝ := fun z => ∑' k : ℕ, P k * z ^ k / (k.factorial : ℝ) with hG
      have hH : ∀ u : ℝ, 0 < u → ShockWear.CumDamage.shockSurv lam P u
          = Real.exp (-(lam * u)) * G (lam * u) := by
        intro u hu
        simp only [ShockWear.CumDamage.shockSurv, ShockWear.CumDamage.poisW,
          if_neg (not_lt.mpr hu.le), hG]
        rw [← tsum_mul_left]
        congr 1; funext k; ring
      have hGnn : ∀ z, 0 ≤ z → 0 ≤ G z := fun z hz =>
        tsum_nonneg (fun k => div_nonneg (mul_nonneg (hnn k) (pow_nonneg hz k)) (by positivity))
      have hGmono : G (lam * s) ≤ G (lam * t) := by
        apply Summable.tsum_le_tsum _ (hsum _ (by positivity)) (hsum _ (by positivity))
        intro k
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (hnn k)
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) k
      have key : G (lam * s) ^ (1 / s) ≤ G (lam * t) ^ (1 / t) := by
        rcases le_or_gt (G (lam * t)) 1 with h1 | h1
        · calc G (lam * s) ^ (1 / s) ≤ G (lam * t) ^ (1 / s) :=
                Real.rpow_le_rpow (hGnn _ (by positivity)) hGmono (by positivity)
            _ ≤ G (lam * t) ^ (1 / t) :=
                Real.rpow_le_rpow_of_exponent_ge' (hGnn _ (by positivity)) h1 (by positivity)
                  (one_div_le_one_div_of_le hs hst)
        · set γ := Real.log (G (lam * t)) / t with hγ
          have hγpos : 0 < γ := div_pos (Real.log_pos h1) ht
          have hGt : G (lam * t) = Real.exp (γ * t) := by
            rw [hγ, div_mul_cancel₀ _ ht.ne', Real.exp_log (by linarith)]
          set β := γ / lam with hβ
          have hβpos : 0 < β := div_pos hγpos hlam
          have hexp : ∀ u : ℝ, Real.exp (γ * u)
              = ∑' k : ℕ, β ^ k * (lam * u) ^ k / (k.factorial : ℝ) := by
            intro u
            have : γ * u = β * (lam * u) := by rw [hβ]; field_simp
            rw [this, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
            show ∑' (n : ℕ), (β * (lam * u)) ^ n / (n.factorial : ℝ) = _
            congr 1; funext k; rw [mul_pow]
          have hsumE : ∀ z : ℝ, Summable (fun k : ℕ => β ^ k * z ^ k / (k.factorial : ℝ)) := by
            intro z
            have := Real.summable_pow_div_factorial (β * z)
            simpa [mul_pow] using this
          have claim : G (lam * s) ≤ Real.exp (γ * s) := by
            set r := s / t with hr
            have hr0 : 0 ≤ r := by positivity
            have hr1 : r ≤ 1 := div_le_one_of_le₀ hst ht.le
            have hC : ∃ C : ℝ, ∀ k : ℕ, (P k - β ^ k) * r ^ k ≤ C * (P k - β ^ k) := by
              classical
              by_cases hex : ∃ k, 1 ≤ k ∧ β ^ k ≤ P k
              · refine ⟨r ^ Nat.find hex, fun k => ?_⟩
                have hm1 : 1 ≤ Nat.find hex := (Nat.find_spec hex).1
                have hmP : β ^ Nat.find hex ≤ P (Nat.find hex) := (Nat.find_spec hex).2
                rcases lt_or_ge k (Nat.find hex) with hk | hk
                · have hneg : P k - β ^ k ≤ 0 := by
                    rcases Nat.eq_zero_or_pos k with h0 | h0
                    · subst h0; simp; exact hP0
                    · have := Nat.find_min hex hk
                      push Not at this
                      linarith [this h0]
                  have : r ^ Nat.find hex ≤ r ^ k := pow_le_pow_of_le_one hr0 hr1 hk.le
                  nlinarith
                · have hpos : 0 ≤ P k - β ^ k := by
                    have h := hroot _ k hm1 hk
                    rw [one_div, one_div] at h
                    have hb : β ≤ P (Nat.find hex) ^ (((Nat.find hex : ℕ) : ℝ)⁻¹) := by
                      calc β = (β ^ Nat.find hex) ^ (((Nat.find hex : ℕ) : ℝ)⁻¹) :=
                            (Real.pow_rpow_inv_natCast hβpos.le (by omega)).symm
                        _ ≤ P (Nat.find hex) ^ (((Nat.find hex : ℕ) : ℝ)⁻¹) :=
                            Real.rpow_le_rpow (by positivity) hmP (by positivity)
                    have : β ^ k ≤ (P k ^ ((k : ℝ)⁻¹)) ^ k :=
                      pow_le_pow_left₀ hβpos.le (hb.trans h) k
                    rw [Real.rpow_inv_natCast_pow (hnn k) (by omega)] at this
                    linarith
                  have : r ^ k ≤ r ^ Nat.find hex := pow_le_pow_of_le_one hr0 hr1 hk
                  nlinarith
              · refine ⟨0, fun k => ?_⟩
                push Not at hex
                have hneg : P k - β ^ k ≤ 0 := by
                  rcases Nat.eq_zero_or_pos k with h0 | h0
                  · subst h0; simp; exact hP0
                  · linarith [hex k h0]
                have : 0 ≤ r ^ k := pow_nonneg hr0 k
                nlinarith
            obtain ⟨C, hC⟩ := hC
            have hs' : lam * s = r * (lam * t) := by rw [hr]; field_simp
            have e1 : G (lam * s) - Real.exp (γ * s) = ∑' k : ℕ,
                (P k - β ^ k) * r ^ k * ((lam * t) ^ k / (k.factorial : ℝ)) := by
              rw [hexp, hG]
              simp only
              rw [← Summable.tsum_sub (hsum _ (by positivity)) (hsumE _)]
              congr 1; funext k; rw [hs', mul_pow]; ring
            have e2 : G (lam * t) - Real.exp (γ * t) = ∑' k : ℕ,
                (P k - β ^ k) * ((lam * t) ^ k / (k.factorial : ℝ)) := by
              rw [hexp, hG]
              simp only
              rw [← Summable.tsum_sub (hsum _ (by positivity)) (hsumE _)]
              congr 1; funext k; ring
            have hsD : Summable (fun k : ℕ => (P k - β ^ k) * ((lam * t) ^ k / (k.factorial : ℝ))) := by
              have := (hsum (lam * t) (by positivity)).sub (hsumE (lam * t))
              refine this.congr (fun k => ?_)
              ring
            have hsD' : Summable (fun k : ℕ =>
                (P k - β ^ k) * r ^ k * ((lam * t) ^ k / (k.factorial : ℝ))) := by
              have := (hsum (lam * s) (by positivity)).sub (hsumE (lam * s))
              refine this.congr (fun k => ?_)
              rw [hs', mul_pow]; ring
            have h3 : ∑' k : ℕ, (P k - β ^ k) * r ^ k * ((lam * t) ^ k / (k.factorial : ℝ))
                ≤ ∑' k : ℕ, C * ((P k - β ^ k) * ((lam * t) ^ k / (k.factorial : ℝ))) := by
              refine Summable.tsum_le_tsum (fun k => ?_) hsD' (hsD.mul_left C)
              have := mul_le_mul_of_nonneg_right (hC k)
                (show (0:ℝ) ≤ (lam * t) ^ k / (k.factorial : ℝ) by positivity)
              linarith [this]
            rw [tsum_mul_left, ← e2, hGt, sub_self, mul_zero, ← e1] at h3
            linarith
          calc G (lam * s) ^ (1 / s) ≤ (Real.exp (γ * s)) ^ (1 / s) :=
                Real.rpow_le_rpow (hGnn _ (by positivity)) claim (by positivity)
            _ = Real.exp γ := by rw [← Real.exp_mul]; congr 1; field_simp
            _ = G (lam * t) ^ (1 / t) := by rw [hGt, ← Real.exp_mul]; congr 1; field_simp
      show ShockWear.CumDamage.shockSurv lam P s ^ (1 / s)
        ≤ ShockWear.CumDamage.shockSurv lam P t ^ (1 / t)
      rw [hH s hs, hH t ht, Real.mul_rpow (Real.exp_pos _).le (hGnn _ (by positivity)),
        Real.mul_rpow (Real.exp_pos _).le (hGnn _ (by positivity)), ← Real.exp_mul, ← Real.exp_mul]
      have e1 : -(lam * s) * (1 / s) = -lam := by field_simp
      have e2 : -(lam * t) * (1 / t) = -lam := by field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
