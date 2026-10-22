-- Prove2me | solution 1 for OutcomeRebate.Transfer.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:48:37.763202+00:00
-- url     : https://prove2.me/submissions/ede4f4db-e478-455d-9f9c-323f7fb83bdb

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_uniform
import Theorems.Thm_OutcomeRebate_Transfer_zq_monotone

namespace OutcomeRebate.Transfer

lemma obp_p1_z_ge_one (P : Params) (hS : P.Standing) : 1 ≤ P.z := by
  obtain ⟨_, _, _, _, _, hq0, hq1, _, _, hlam, _⟩ := hS
  have hk : 0 < P.lam * (1 - P.q) / P.q := div_pos (mul_pos (by linarith) (by linarith)) hq0
  have := Real.rpow_nonneg hk.le (1 / P.α)
  show 1 ≤ 1 + (P.lam * (1 - P.q) / P.q) ^ (1 / P.α)
  linarith

/-- `ΔU = W(β) − W(1)` for prices with `pz ≤ v̄`. -/
lemma obp_p1_diff_low (P : Params) (hS : P.Standing) (p : ℝ) (hp : 0 ≤ p)
    (hpv : p * P.z ≤ P.vbar) :
    payerObjU P P.β p - payerObjU P 1 p = P.n / P.vbar *
      ((1 - P.β) * p * P.z * (P.q * P.vp - p * (1 - P.q * P.z * (1 + P.β) / 2))) := by
  have hβ := hS.2.2.2.1
  have hβh := hS.2.2.2.2.1
  have hz1 := obp_p1_z_ge_one P hS
  rw [(closed_forms_uniform P hS P.β p (Or.inl rfl) hp).2,
    (closed_forms_uniform P hS 1 p (Or.inr rfl) hp).2]
  have h0 : 0 ≤ p * P.z := mul_nonneg hp (by linarith)
  have h1 : max (P.vbar - P.β * p * P.z) 0 = P.vbar - P.β * p * P.z := by
    apply max_eq_left; nlinarith
  have h2 : max (P.vbar - 1 * p * P.z) 0 = P.vbar - 1 * p * P.z := by
    apply max_eq_left; linarith
  rw [h1, h2]; ring

end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

set_option maxHeartbeats 1000000 in
theorem solution (P : Params) (hS : P.Standing) (q1 q2 : ℝ)
    (hq1 : 0 < q1 ∧ q1 < 1 ∧ zOf P.α P.lam q1 * q1 = 2 / P.β)
    (hq2 : 0 < q2 ∧ q2 < 1 ∧ zOf P.α P.lam q2 * q2 = 2 / (1 + P.β)) :
    let p1 := P.q * (P.vp + P.vbar / 2) / (1 - P.q * P.z * P.β / 2)
    let p2 := P.q * P.vp / (1 - P.q * P.z * (1 + P.β) / 2)
    (q1 < q2 ∧ q2 < q0 P.α P.lam) ∧
    (∀ p : ℝ, P.vbar / (P.β * P.z) ≤ p → payerObjU P 1 p = payerObjU P P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / (P.β * P.z) →
      (P.q ≤ q1 → coversU P p) ∧
      (q1 < P.q → P.q ≤ q2 →
        (p ≤ P.vbar / P.z → coversU P p) ∧ (P.vbar / P.z < p → (coversU P p ↔ p ≤ p1))) ∧
      (q2 < P.q →
        (p ≤ P.vbar / P.z → (coversU P p ↔ p ≤ p2)) ∧
          (P.vbar / P.z < p → (coversU P p ↔ p ≤ p1)))) := by
  intro p1 p2
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hz1 := obp_p1_z_ge_one P hS
  have hM := zq_monotone P.α P.lam ⟨hα0, hα1⟩ hlam
  have hk1 : (1:ℝ) < 2 / P.β := by rw [lt_div_iff₀ hβ]; linarith
  have hk2 : (1:ℝ) < 2 / (1 + P.β) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hk12 : 2 / (1 + P.β) < 2 / P.β := by
    apply div_lt_div_of_pos_left (by norm_num) hβ (by linarith)
  have K1r := hM.2.2.2 (2 / P.β) q1 hk1 hq1.1 hq1.2.1 hq1.2.2
  have K2r := hM.2.2.2 (2 / (1 + P.β)) q2 hk2 hq2.1 hq2.2.1 hq2.2.2
  have K1 : 2 / P.β ≤ P.z * P.q ↔ P.q ≤ q1 := K1r P.q hq0 hqlt
  have K2 : 2 / (1 + P.β) ≤ P.z * P.q ↔ P.q ≤ q2 := K2r P.q hq0 hqlt
  have K21 : 2 / (1 + P.β) ≤ zOf P.α P.lam q1 * q1 ↔ q1 ≤ q2 := K2r q1 hq1.1 hq1.2.1
  have hN : 0 < P.n / P.vbar := div_pos hn hv
  have hbz : 0 < P.β * P.z := by positivity
  refine ⟨⟨?_, ?_⟩, fun p hp => ?_, fun p hp0 hp => ?_⟩
  · -- q1 < q2
    have h12 : q1 ≤ q2 := K21.mp (by rw [hq1.2.2]; exact hk12.le)
    rcases eq_or_lt_of_le h12 with h | h
    · exfalso; rw [h] at hq1; rw [hq1.2.2] at hq2; linarith [hq2.2.2]
    · exact h
  · -- q2 < q0
    by_contra hc'
    push Not at hc'
    have := hM.2.2.1 q2 ⟨hc', hq2.2.1.le⟩
    linarith [hq2.2.2]
  · -- (a) indifference
    have hp0 : 0 ≤ p := le_trans (div_pos hv hbz).le hp
    rw [(closed_forms_uniform P hS P.β p (Or.inl rfl) hp0).2,
      (closed_forms_uniform P hS 1 p (Or.inr rfl) hp0).2]
    rw [div_le_iff₀ hbz] at hp
    have h1 : max (P.vbar - P.β * p * P.z) 0 = 0 := by apply max_eq_right; nlinarith
    have h2 : max (P.vbar - 1 * p * P.z) 0 = 0 := by
      apply max_eq_right
      have : P.β * p * P.z ≤ 1 * p * P.z := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_right (by linarith) hp0
      nlinarith
    rw [h1, h2]; simp
  · -- (b)
    have hpz : P.β * p * P.z < P.vbar := by
      rw [lt_div_iff₀ hbz] at hp; linarith
    have hpzpos : 0 ≤ p * P.z := mul_nonneg hp0 (by linarith)
    -- high-price branch: `pz > v̄`
    have high : P.vbar / P.z < p → P.q * P.z * P.β / 2 < 1 → (coversU P p ↔ p ≤ p1) := by
      intro hpv hD
      rw [div_lt_iff₀ (by linarith)] at hpv
      unfold coversU
      rw [(closed_forms_uniform P hS P.β p (Or.inl rfl) hp0).2,
        (closed_forms_uniform P hS 1 p (Or.inr rfl) hp0).2]
      have h1 : max (P.vbar - P.β * p * P.z) 0 = P.vbar - P.β * p * P.z := by
        apply max_eq_left; linarith
      have h2 : max (P.vbar - 1 * p * P.z) 0 = 0 := by apply max_eq_right; linarith
      rw [h1, h2]
      simp only [mul_zero, zero_mul]
      have hpos : 0 < P.n / P.vbar * (P.vbar - P.β * p * P.z) := mul_pos hN (by linarith)
      show _ ↔ p ≤ P.q * (P.vp + P.vbar / 2) / (1 - P.q * P.z * P.β / 2)
      rw [le_div_iff₀ (by linarith)]
      constructor
      · intro h
        have : 0 ≤ P.q * P.vp - p + P.q / 2 * (P.vbar + P.β * p * P.z) := by
          by_contra hc'
          push Not at hc'
          have := mul_neg_of_pos_of_neg hpos hc'
          linarith
        nlinarith
      · intro h
        apply mul_nonneg hpos.le
        nlinarith
    -- low-price branch: covers iff the bracket is nonnegative (or p = 0)
    have low : p ≤ P.vbar / P.z → (coversU P p ↔
        (p = 0 ∨ p * (1 - P.q * P.z * (1 + P.β) / 2) ≤ P.q * P.vp)) := by
      intro hpv
      rw [le_div_iff₀ (by linarith)] at hpv
      unfold coversU
      rw [← sub_nonneg, obp_p1_diff_low P hS p hp0 hpv]
      have h1β : 0 < 1 - P.β := by linarith
      constructor
      · intro h
        rcases eq_or_lt_of_le hp0 with h0 | h0
        · left; exact h0.symm
        · right
          have hpos : 0 < P.n / P.vbar * ((1 - P.β) * p * P.z) :=
            mul_pos hN (mul_pos (mul_pos h1β h0) (by linarith))
          by_contra hc'
          push Not at hc'
          have := mul_neg_of_pos_of_neg hpos (by linarith :
            P.q * P.vp - p * (1 - P.q * P.z * (1 + P.β) / 2) < 0)
          nlinarith
      · rintro (h | h)
        · rw [h]; simp
        · apply mul_nonneg hN.le
          apply mul_nonneg (mul_nonneg (mul_nonneg h1β.le hp0) (by linarith))
          linarith
    refine ⟨fun hq => ?_, fun hq hq' => ⟨fun hpv => ?_, fun hpv => ?_⟩, fun hq => ⟨fun hpv => ?_,
      fun hpv => ?_⟩⟩
    · -- q ≤ q1: zq ≥ 2/β
      have hzq : 2 / P.β ≤ P.z * P.q := K1.mpr hq
      have hzq' : 1 ≤ P.q * P.z * P.β / 2 := by
        rw [div_le_iff₀ hβ] at hzq; nlinarith
      rcases le_or_gt p (P.vbar / P.z) with hpv | hpv
      · rw [low hpv]; right
        have : p * (1 - P.q * P.z * (1 + P.β) / 2) ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos hp0
          nlinarith [mul_pos (mul_pos hq0 (by linarith : (0:ℝ) < P.z)) hβ]
        nlinarith [mul_nonneg hq0.le hvp]
      · rw [div_lt_iff₀ (by linarith)] at hpv
        unfold coversU
        rw [(closed_forms_uniform P hS P.β p (Or.inl rfl) hp0).2,
          (closed_forms_uniform P hS 1 p (Or.inr rfl) hp0).2]
        have h2 : max (P.vbar - 1 * p * P.z) 0 = 0 := by apply max_eq_right; linarith
        rw [h2]
        simp only [mul_zero, zero_mul]
        apply mul_nonneg (mul_nonneg hN.le (le_max_right _ _))
        nlinarith [mul_nonneg hq0.le hvp, mul_nonneg hq0.le hv.le]
    · -- q1 < q ≤ q2, low prices
      have hzq : 2 / (1 + P.β) ≤ P.z * P.q := K2.mpr hq'
      have hzq' : 1 ≤ P.q * P.z * (1 + P.β) / 2 := by
        rw [div_le_iff₀ (by linarith)] at hzq; nlinarith
      rw [low hpv]; right
      have : p * (1 - P.q * P.z * (1 + P.β) / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp0 (by linarith)
      nlinarith [mul_nonneg hq0.le hvp]
    · -- q1 < q ≤ q2, high prices
      apply high hpv
      have : ¬ (2 / P.β ≤ P.z * P.q) := fun h => absurd (K1.mp h) (not_le.mpr hq)
      push Not at this
      rw [lt_div_iff₀ hβ] at this
      nlinarith
    · -- q > q2, low prices
      have hzq : P.z * P.q < 2 / (1 + P.β) := by
        by_contra h; push Not at h; exact absurd (K2.mp h) (not_le.mpr hq)
      have hD : 0 < 1 - P.q * P.z * (1 + P.β) / 2 := by
        rw [lt_div_iff₀ (by linarith)] at hzq; nlinarith
      rw [low hpv]
      show _ ↔ p ≤ P.q * P.vp / (1 - P.q * P.z * (1 + P.β) / 2)
      rw [le_div_iff₀ hD]
      constructor
      · rintro (h | h)
        · rw [h]; nlinarith [mul_nonneg hq0.le hvp]
        · linarith
      · intro h; right; linarith
    · -- q > q2, high prices
      apply high hpv
      have hzq : P.z * P.q < 2 / (1 + P.β) := by
        by_contra h; push Not at h; exact absurd (K2.mp h) (not_le.mpr hq)
      have : P.z * P.q < 2 / P.β := lt_trans hzq hk12
      rw [lt_div_iff₀ hβ] at this
      nlinarith
