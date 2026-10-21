-- Prove2me | solution 1 for PlatformEntry.Protective.eq9_eq10_benchmarks
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:29:36.395031+00:00
-- url     : https://prove2.me/submissions/79a3e5e4-59ae-49b8-adfe-b2a103ba20d0

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

theorem solution (δ f β cS a : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) (hcS : 1 / 2 < cS) :
    (∀ e : ℝ, e ≠ eBN f cS a → PlatformEntry.Regimes.profitN δ f β cS a e < PlatformEntry.Regimes.profitN δ f β cS a (eBN f cS a)) ∧
      ((1 - f) * (1 + 4 * PlatformEntry.Regimes.H δ f β) < 4 * cS →
        ∀ e : ℝ, e ≠ eBE δ f β cS a →
          PlatformEntry.Regimes.profitE δ f β cS a e < PlatformEntry.Regimes.profitE δ f β cS a (eBE δ f β cS a)) := by
  have hκ := PEPH.kappa_pos f cS hf0 hcS
  constructor
  · intro e he
    rw [PEPH.profitN_eq δ f β cS a e hκ]
    have : 0 < (e - eBN f cS a) ^ 2 := by
      have : e - eBN f cS a ≠ 0 := sub_ne_zero.mpr he
      positivity
    have : 0 < (f + 2 * cS - 1) / 2 * (e - eBN f cS a) ^ 2 := by positivity
    linarith
  · intro hμ e he
    rw [PEPH.profitE_eq δ f β cS a e hμ]
    have h : 0 < 4 * cS - (1 - f) * (1 + 4 * H δ f β) := by linarith
    have : 0 < (e - eBE δ f β cS a) ^ 2 := by
      have : e - eBE δ f β cS a ≠ 0 := sub_ne_zero.mpr he
      positivity
    have : 0 < (4 * cS - (1 - f) * (1 + 4 * H δ f β)) / 4 * (e - eBE δ f β cS a) ^ 2 := by positivity
    linarith
