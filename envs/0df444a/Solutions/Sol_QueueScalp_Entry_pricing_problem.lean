-- Prove2me | solution 1 for QueueScalp.Entry.pricing_problem
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:16:15.814972+00:00
-- url     : https://prove2.me/submissions/9f589a55-4e82-4721-8fdf-1d09f6ae4d2c

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

open QueueScalp.Entry

namespace QSPricingAux

lemma den_eq (mu Lam cS ct : ℝ) (hc : cS ≠ 0) :
    mu - Lam * cS + Lam * cS * ((cS - ct) / cS) = mu - Lam * ct := by
  field_simp; ring

lemma D_eq (mu Lam cS ct : ℝ) (hc : cS ≠ 0) :
    D mu (Lam * cS) ((cS - ct) / cS) = (Lam * cS / mu) ^ 2 / (mu - Lam * ct) := by
  unfold D W1 W2
  rw [den_eq mu Lam cS ct hc]
  have : (Lam * cS / mu) ^ 2 * ((cS - ct) / cS) / (mu - Lam * ct) +
      (Lam * cS / mu) ^ 2 * (1 - (cS - ct) / cS) / (mu - Lam * ct) =
      (Lam * cS / mu) ^ 2 / (mu - Lam * ct) := by
    rw [← add_div, ← mul_add]; congr 1; ring
  linarith

lemma join_eq (mu Lam cS ct : ℝ) (hmu : 0 < mu) (hc : 0 < cS) (hst : Lam * cS < mu)
    (hct : Lam * ct ≤ Lam * cS) :
    cS * W1 mu (Lam * cS) ((cS - ct) / cS) + ct * D mu (Lam * cS) ((cS - ct) / cS) =
      cS / (mu - Lam * cS) := by
  rw [D_eq mu Lam cS ct hc.ne']
  unfold W1
  rw [den_eq mu Lam cS ct hc.ne']
  have h1 : mu - Lam * cS ≠ 0 := by linarith
  have h2 : mu - Lam * ct ≠ 0 := by linarith
  have h3 : mu ≠ 0 := hmu.ne'
  have h4 : cS ≠ 0 := hc.ne'
  field_simp
  ring

end QSPricingAux

open QSPricingAux in
theorem solution (P : Params) (hS : P.Standing) (Lam : ℝ)
    (hLam : 0 < Lam) :
    (∀ price lam q cS ct : ℝ, 0 ≤ price →
      IsCustEq P Lam price lam q cS ct →
      price * lam * q =
        Lam ^ 3 * cS ^ 2 * ct * (cS - ct) /
          (P.mu ^ 2 * (P.mu - Lam * ct))) ∧
    (∀ ct ∈ Set.Icc (0 : ℝ) (cSOf P Lam),
      ∃ price lam q : ℝ,
        price = ct * D P.mu (Lam * cSOf P Lam)
          ((cSOf P Lam - ct) / cSOf P Lam) ∧
        0 ≤ price ∧
        IsCustEq P Lam price lam q (cSOf P Lam) ct) := by
  obtain ⟨hmu, hV, -⟩ := hS
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  constructor
  · intro price lam q cS ct _ he
    have hc : cS ≠ 0 := he.cS_pos.ne'
    have hD : W2 P.mu lam q - W1 P.mu lam q = (Lam * cS / P.mu) ^ 2 / (P.mu - Lam * ct) := by
      have := D_eq P.mu Lam cS ct hc
      rw [he.thru, he.rate]; exact this
    rw [he.indiff, hD, he.thru, he.rate]
    by_cases h0 : P.mu - Lam * ct = 0
    · simp [h0]
    · have h3 : P.mu ≠ 0 := hmu.ne'
      field_simp
  · rintro ct ⟨hct0, hctc⟩
    set cS := cSOf P Lam with hcS
    -- properties of cS
    have hprop : 0 < cS ∧ cS ≤ 1 ∧ Lam * cS < P.mu ∧
        (1 - cS) * (P.V - cS / (P.mu - Lam * cS)) = 0 ∧ 0 ≤ P.V - cS / (P.mu - Lam * cS) := by
      simp only [hcS, cSOf]
      split_ifs with h
      · have hlt : Lam < P.mu := by have : 0 < 1 / P.V := by positivity
                                    linarith
        refine ⟨one_pos, le_rfl, by linarith, by ring, ?_⟩
        rw [sub_nonneg, mul_one, div_le_iff₀ (by linarith)]
        have : 1 / P.V ≤ P.mu - Lam := by linarith
        rw [div_le_iff₀ hV0] at this
        linarith
      · push Not at h
        have hLV : 0 < 1 + Lam * P.V := by positivity
        have hle : P.mu * P.V ≤ 1 + Lam * P.V := by
          have h1 : P.mu - Lam < 1 / P.V := by linarith
          rw [lt_div_iff₀ hV0] at h1
          nlinarith
        have hst : Lam * (P.mu * P.V / (1 + Lam * P.V)) < P.mu := by
          rw [mul_div_assoc', div_lt_iff₀ hLV]; nlinarith
        have hden : P.mu - Lam * (P.mu * P.V / (1 + Lam * P.V)) = P.mu / (1 + Lam * P.V) := by
          field_simp; ring
        have hval : P.mu * P.V / (1 + Lam * P.V) / (P.mu - Lam * (P.mu * P.V / (1 + Lam * P.V)))
            = P.V := by
          rw [hden]; field_simp
        refine ⟨by positivity, by rw [div_le_one hLV]; exact hle, hst, ?_, ?_⟩
        · rw [hval]; ring
        · rw [hval]; simp
    obtain ⟨hc0, hc1, hst, hslack, hjoin⟩ := hprop
    have hctc' : Lam * ct ≤ Lam * cS := mul_le_mul_of_nonneg_left hctc hLam.le
    have hJ := join_eq P.mu Lam cS ct hmu hc0 hst hctc'
    have hDnn : 0 ≤ D P.mu (Lam * cS) ((cS - ct) / cS) := by
      rw [D_eq P.mu Lam cS ct hc0.ne']
      apply div_nonneg (sq_nonneg _); linarith
    refine ⟨ct * D P.mu (Lam * cS) ((cS - ct) / cS), Lam * cS, (cS - ct) / cS, rfl,
      mul_nonneg hct0 hDnn, ?_⟩
    exact {
      ct_nonneg := hct0
      ct_le_cS := hctc
      cS_pos := hc0
      cS_le_one := hc1
      stable := hst
      join := by
        have : P.V - cS * W1 P.mu (Lam * cS) ((cS - ct) / cS) -
            ct * D P.mu (Lam * cS) ((cS - ct) / cS) = P.V - cS / (P.mu - Lam * cS) := by
          rw [← hJ]; ring
        rw [this]; exact hjoin
      slack := by
        have : P.V - cS * W1 P.mu (Lam * cS) ((cS - ct) / cS) -
            ct * D P.mu (Lam * cS) ((cS - ct) / cS) = P.V - cS / (P.mu - Lam * cS) := by
          rw [← hJ]; ring
        rw [this]; exact hslack
      indiff := rfl
      thru := rfl
      rate := rfl }
