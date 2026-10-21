-- Prove2me | solution 1 for PlatformEntry.Protective.case_1_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:33:22.46997+00:00
-- url     : https://prove2.me/submissions/e4830b3b-8851-4a3e-9a3f-956ebb6292b9

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

set_option autoImplicit false
open PlatformEntry.Protective PlatformEntry.Regimes

namespace PEPH

lemma H_nonneg (δ f β : ℝ) : 0 ≤ H δ f β := by
  unfold H
  split_ifs
  · positivity
  · exact le_refl _

lemma kappa_pos (f cS : ℝ) (hf0 : 0 ≤ f) (hcS : 1 / 2 < cS) : 0 < f + 2 * cS - 1 := by linarith

lemma w_le (δ f β : ℝ) (hf1 : f < 1) (hprot : H δ f β ≤ 1 / 4) :
    (1 - f) * (1 + 4 * H δ f β) ≤ 2 * (1 - f) := by nlinarith

lemma w_lt (δ f β cS : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) (hcS : 1 / 2 < cS) (hprot : H δ f β ≤ 1 / 4) :
    (1 - f) * (1 + 4 * H δ f β) < 4 * cS := by
  have := w_le δ f β hf1 hprot
  linarith

lemma profitN_eq (δ f β cS a e : ℝ) (hκ : 0 < f + 2 * cS - 1) :
    profitN δ f β cS a e = profitN δ f β cS a (eBN f cS a) - (f + 2 * cS - 1) / 2 * (e - eBN f cS a) ^ 2 := by
  unfold profitN eBN
  field_simp
  ring

lemma quadE (W cS a e : ℝ) (hW : 4 * cS - W ≠ 0) :
    W / 4 * (a + e) ^ 2 - cS * e ^ 2
      = (W / 4 * (a + a * W / (4 * cS - W)) ^ 2 - cS * (a * W / (4 * cS - W)) ^ 2)
        - (4 * cS - W) / 4 * (e - a * W / (4 * cS - W)) ^ 2 := by
  field_simp
  ring

lemma Qlem (W cS : ℝ) (hd : 4 * cS - W ≠ 0) :
    W / 4 * (1 + W / (4 * cS - W)) ^ 2 - cS * (W / (4 * cS - W)) ^ 2 = cS * (W / (4 * cS - W)) := by
  field_simp
  ring

lemma profitE_eq (δ f β cS a e : ℝ) (hμ : (1 - f) * (1 + 4 * H δ f β) < 4 * cS) :
    profitE δ f β cS a e = profitE δ f β cS a (eBE δ f β cS a)
      - (4 * cS - (1 - f) * (1 + 4 * H δ f β)) / 4 * (e - eBE δ f β cS a) ^ 2 := by
  have hne : 4 * cS - (1 - f) * (1 + 4 * H δ f β) ≠ 0 := by linarith
  have h := quadE ((1 - f) * (1 + 4 * H δ f β)) cS a e hne
  have e1 : ∀ x : ℝ, profitE δ f β cS a x = (1 - f) * (1 + 4 * H δ f β) / 4 * (a + x) ^ 2 - cS * x ^ 2 := by
    intro x; unfold profitE; ring
  have e2 : eBE δ f β cS a = a * ((1 - f) * (1 + 4 * H δ f β)) / (4 * cS - (1 - f) * (1 + 4 * H δ f β)) := by
    unfold eBE; ring
  rw [e1 e, e1 (eBE δ f β cS a), e2]
  exact h

lemma profitE_le_profitN (δ f β cS a e : ℝ) (hf1 : f < 1) (hprot : H δ f β ≤ 1 / 4) :
    profitE δ f β cS a e ≤ profitN δ f β cS a e := by
  unfold profitE profitN
  have h1 : 0 ≤ (1 - f) := by linarith
  have h2 : 0 ≤ (1 - f) * (a + e) ^ 2 := by positivity
  nlinarith

lemma profitN_le (δ f β cS a e : ℝ) (hκ : 0 < f + 2 * cS - 1) :
    profitN δ f β cS a e ≤ profitN δ f β cS a (eBN f cS a) := by
  rw [profitN_eq δ f β cS a e hκ]
  have : 0 ≤ (f + 2 * cS - 1) / 2 * (e - eBN f cS a) ^ 2 := by positivity
  linarith

lemma profitE_le (δ f β cS a e : ℝ) (hμ : (1 - f) * (1 + 4 * H δ f β) < 4 * cS) :
    profitE δ f β cS a e ≤ profitE δ f β cS a (eBE δ f β cS a) := by
  rw [profitE_eq δ f β cS a e hμ]
  have h : 0 < 4 * cS - (1 - f) * (1 + 4 * H δ f β) := by linarith
  have : 0 ≤ (4 * cS - (1 - f) * (1 + 4 * H δ f β)) / 4 * (e - eBE δ f β cS a) ^ 2 := by positivity
  linarith

lemma sellerTotal_le (δ f β cS K a e : ℝ) (h : e + a ≤ Delta δ f β K) :
    sellerTotal δ f β cS K a e = profitN δ f β cS a e := by
  unfold sellerTotal
  rw [if_pos h]

lemma sellerTotal_gt (δ f β cS K a e : ℝ) (h : Delta δ f β K < e + a) :
    sellerTotal δ f β cS K a e = profitE δ f β cS a e := by
  unfold sellerTotal
  rw [if_neg (not_le.mpr h)]

lemma a_add_eBN (f cS a : ℝ) (hκ : 0 < f + 2 * cS - 1) :
    a + eBN f cS a = a * (2 * cS / (f + 2 * cS - 1)) := by
  unfold eBN
  field_simp
  ring

lemma r_pos (f cS : ℝ) (hκ : 0 < f + 2 * cS - 1) (hcS : 1 / 2 < cS) : 0 < 2 * cS / (f + 2 * cS - 1) := by
  apply div_pos <;> linarith

end PEPH

theorem solution (δ f β cS K : ℝ) (hbox : PlatformEntry.Regimes.InBox δ f β) (hcS : 1 / 2 < cS) (hK : 0 < K)
    (h5 : PlatformEntry.Regimes.cond5 δ f β) (hprot : PlatformEntry.Regimes.H δ f β ≤ 1 / 4) (a₁ : ℝ)
    (ha₁ : a₁ + eBN f cS a₁ = Delta δ f β K) :
    ∀ a : ℝ, a₁ ≤ a → Mfun δ f β cS K a ≤ 0 → Delta δ f β K < a + eBE δ f β cS a →
      IsOptimalEffort δ f β cS K a (eBE δ f β cS a) := by
  intro a ha hM hgt
  obtain ⟨_, _, hf0, hf1, _, _⟩ := hbox
  have hκ := PEPH.kappa_pos f cS hf0 hcS
  have hr := PEPH.r_pos f cS hκ hcS
  have hμ := PEPH.w_lt δ f β cS hf0 hf1 hcS hprot
  have hcut : Delta δ f β K - a ≤ eBN f cS a := by
    have h1 := PEPH.a_add_eBN f cS a hκ
    have h2 := PEPH.a_add_eBN f cS a₁ hκ
    have : a₁ * (2 * cS / (f + 2 * cS - 1)) ≤ a * (2 * cS / (f + 2 * cS - 1)) :=
      mul_le_mul_of_nonneg_right ha hr.le
    linarith
  intro e'
  have hgt' : Delta δ f β K < eBE δ f β cS a + a := by linarith
  rw [PEPH.sellerTotal_gt δ f β cS K a _ hgt']
  by_cases he : e' + a ≤ Delta δ f β K
  · rw [PEPH.sellerTotal_le δ f β cS K a _ he]
    rw [PEPH.profitN_eq δ f β cS a e' hκ]
    have h1 : e' ≤ Delta δ f β K - a := by linarith
    have h2 : (Delta δ f β K - a - eBN f cS a) ^ 2 ≤ (e' - eBN f cS a) ^ 2 := by
      nlinarith
    have h3 : (f + 2 * cS - 1) / 2 * (Delta δ f β K - a - eBN f cS a) ^ 2 ≤ (f + 2 * cS - 1) / 2 * (e' - eBN f cS a) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 := PEPH.profitN_eq δ f β cS a (Delta δ f β K - a) hκ
    unfold Mfun at hM
    linarith
  · rw [PEPH.sellerTotal_gt δ f β cS K a _ (not_le.mp he)]
    exact PEPH.profitE_le δ f β cS a e' hμ
