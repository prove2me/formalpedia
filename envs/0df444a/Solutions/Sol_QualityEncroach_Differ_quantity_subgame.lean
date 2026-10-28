-- Prove2me | solution 1 for QualityEncroach.Differ.quantity_subgame
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:28:36.99193+00:00
-- url     : https://prove2.me/submissions/e3423c14-cbc9-44a0-8cd0-b11793bc6464

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game
import Definitions.Def_QualityEncroach_Differ_Reduced

open QualityEncroach.Differ in
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w u t : ℝ) (hu : 0 < u)
    (ht0 : 0 < t) (ht1 : t < 1) (hqR : 0 ≤ qR7 k c w u t) (hqM : 0 ≤ qM7 k c w u t) :
    (∀ qM : ℝ, 0 ≤ qM →
      mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM⟩ ≤
        mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩) ∧
    (∀ qR qM : ℝ, 0 ≤ qR → 0 ≤ qM →
      (∀ qM' : ℝ, 0 ≤ qM' → mfrPayoff k c ⟨w, u, t, qR, qM'⟩ ≤ mfrPayoff k c ⟨w, u, t, qR, qM⟩) →
      retailerPayoff ⟨w, u, t, qR, qM⟩ ≤
        retailerPayoff ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩) := by
  have ht1' : t ≤ 1 := ht1.le
  have hu0 : u ≠ 0 := hu.ne'
  have ht0' : t ≠ 0 := ht0.ne'
  have h2t : (2 - t) ≠ 0 := by intro h; linarith
  set qi : ℝ → ℝ := fun qR => (1 - t * qR - c / u - k * u) / 2 with hqi
  have hmfr : ∀ qR qM, mfrPayoff k c ⟨w, u, t, qR, qM⟩ =
      (w - k * (t * u) ^ 2) * qR + u * qi qR ^ 2 - u * (qM - qi qR) ^ 2 := by
    intro qR qM
    simp only [mfrPayoff, priceM, if_pos ht1', hqi]
    field_simp
    ring
  have hq7 : qM7 k c w u t = qi (qR7 k c w u t) := by
    simp only [qM7, qR7, hqi]
    field_simp
    ring
  have hret : ∀ qR qM, retailerPayoff ⟨w, u, t, qR, qM⟩ = (t * u * (1 - qM - qR) - w) * qR := by
    intro qR qM
    simp only [retailerPayoff, priceR, if_pos ht1']
  refine ⟨fun qM _ => ?_, fun qR qM hqR0 hqM0 hBR => ?_⟩
  · rw [hmfr, hmfr, hq7, sub_self]
    nlinarith [sq_nonneg (qM - qi (qR7 k c w u t))]
  · have hge : qi qR ≤ qM := by
      by_contra hlt
      push_neg at hlt
      have h1 := hBR (qi qR) (by linarith)
      rw [hmfr, hmfr, sub_self] at h1
      have : u * (qM - qi qR) ^ 2 ≤ 0 := by nlinarith
      have : (qM - qi qR) ^ 2 ≤ 0 := by
        by_contra h2; push_neg at h2; nlinarith
      have : qM - qi qR = 0 := by nlinarith [sq_nonneg (qM - qi qR)]
      linarith
    have hf : ∀ q, (t * u * (1 - qi q - q) - w) * q =
        (t * u * (1 - qi (qR7 k c w u t) - qR7 k c w u t) - w) * qR7 k c w u t -
          t * u * (1 - t / 2) * (q - qR7 k c w u t) ^ 2 := by
      intro q
      simp only [hqi, qR7]
      field_simp
      ring
    rw [hret, hret, hq7]
    have step1 : (t * u * (1 - qM - qR) - w) * qR ≤ (t * u * (1 - qi qR - qR) - w) * qR := by
      have : 0 ≤ t * u * qR := by positivity
      nlinarith
    have step2 := hf qR
    have hpos : 0 ≤ t * u * (1 - t / 2) * (qR - qR7 k c w u t) ^ 2 := by
      have : 0 < 1 - t / 2 := by linarith
      positivity
    linarith
