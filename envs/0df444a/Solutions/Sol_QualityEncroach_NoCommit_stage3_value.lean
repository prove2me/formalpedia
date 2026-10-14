-- Prove2me | solution 1 for QualityEncroach.NoCommit.stage3_value
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:01:30.528781+00:00
-- url     : https://prove2.me/submissions/bc5c3987-7797-40f4-99f9-41276c2159d8

import Definitions.Def_QualityEncroach_NoCommit_Game
open QualityEncroach.NoCommit

private lemma quad_max (a b q : ℝ) (ha : 0 < a) (hq : 0 ≤ q) :
    (b - a * q) * q ≤ (b - a * max 0 (b / (2*a))) * max 0 (b / (2*a)) := by
  have hden : 2*a ≠ 0 := by positivity
  have he : b / (2*a) * (2*a) = b := div_mul_cancel₀ b hden
  by_cases h : 0 ≤ b / (2*a)
  · rw [max_eq_right h]
    nlinarith [mul_nonneg ha.le (sq_nonneg (q - b/(2*a)))]
  · have hb : b ≤ 0 := by
      have hn := mul_neg_of_neg_of_pos (lt_of_not_ge h) (show 0 < 2*a by positivity)
      linarith
    rw [max_eq_left (le_of_lt (lt_of_not_ge h))]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hb hq, mul_nonneg ha.le (sq_nonneg q)]

private lemma quad_value (a b : ℝ) (ha : 0 < a) (h : 0 < max 0 (b/(2*a))) :
    (b - a * max 0 (b/(2*a))) * max 0 (b/(2*a)) = b^2/(4*a) := by
  have hb : 0 < b/(2*a) := by simpa only [lt_max_iff, lt_self_iff_false, false_or] using h
  rw [max_eq_right hb.le]
  field_simp
  <;> ring
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w uR qR τ : ℝ)
    (huR : 0 < uR) (hqR : 0 ≤ qR) (hτ : 0 < τ) :
    (1 ≤ τ →
      (∀ qM : ℝ, 0 ≤ qM →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qM⟩ ≤
          mfrPayoff k c ⟨w, uR, qR, τ * uR, qMHF k c τ qR uR⟩) ∧
      (0 < qMHF k c τ qR uR →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qMHF k c τ qR uR⟩ = PiHF k c τ qR uR w)) ∧
    (τ ≤ 1 →
      (∀ qM : ℝ, 0 ≤ qM →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qM⟩ ≤
          mfrPayoff k c ⟨w, uR, qR, τ * uR, qMLF k c τ qR uR⟩) ∧
      (0 < qMLF k c τ qR uR →
        mfrPayoff k c ⟨w, uR, qR, τ * uR, qMLF k c τ qR uR⟩ = PiLF k c τ qR uR w)) ∧
    PiHF k c 1 qR uR w = PiLF k c 1 qR uR w := by
  have ha : 0 < τ * uR := mul_pos hτ huR
  have hpH (q : ℝ) (ht : 1 ≤ τ) :
      priceM (τ*uR) uR q qR = τ*uR*(1-q)-uR*qR := by
    unfold priceM
    rw [if_pos (by nlinarith)]
  have hpL (q : ℝ) (ht : τ ≤ 1) :
      priceM (τ*uR) uR q qR = τ*uR*(1-q-qR) := by
    unfold priceM
    split_ifs with h
    · have he : τ = 1 := by nlinarith
      rw [he]; ring
    · rfl
  constructor
  · intro ht
    have hform (q : ℝ) : mfrPayoff k c ⟨w,uR,qR,τ*uR,q⟩ =
        (w-k*uR^2)*qR + ((-c-qR*uR-k*(τ^2*uR^2)+τ*uR)-(τ*uR)*q)*q := by
      simp only [mfrPayoff, hpH q ht]
      ring
    constructor
    · intro q hq
      simp only [hform, qMHF]
      exact add_le_add le_rfl (by simpa only [mul_assoc] using quad_max (τ*uR) (-c-qR*uR-k*(τ^2*uR^2)+τ*uR) q ha hq)
    · intro hq
      rw [hform]
      have hv := quad_value (τ*uR) (-c-qR*uR-k*(τ^2*uR^2)+τ*uR) ha (by simpa only [qMHF, mul_assoc] using hq)
      change (w-k*uR^2)*qR + _ = _
      rw [show qMHF k c τ qR uR = max 0 ((-c-qR*uR-k*(τ^2*uR^2)+τ*uR)/(2*(τ*uR))) by unfold qMHF; ring_nf]
      rw [hv]
      unfold PiHF
      ring
  · constructor
    · intro ht
      have hform (q : ℝ) : mfrPayoff k c ⟨w,uR,qR,τ*uR,q⟩ =
          (w-k*uR^2)*qR + ((-c-τ*uR*(qR+k*τ*uR-1))-(τ*uR)*q)*q := by
        simp only [mfrPayoff, hpL q ht]
        ring
      constructor
      · intro q hq
        simp only [hform, qMLF]
        exact add_le_add le_rfl (by simpa only [mul_assoc] using quad_max (τ*uR) (-c-τ*uR*(qR+k*τ*uR-1)) q ha hq)
      · intro hq
        rw [hform]
        have hv := quad_value (τ*uR) (-c-τ*uR*(qR+k*τ*uR-1)) ha (by simpa only [qMLF, mul_assoc] using hq)
        rw [show qMLF k c τ qR uR = max 0 ((-c-τ*uR*(qR+k*τ*uR-1))/(2*(τ*uR))) by unfold qMLF; ring_nf]
        rw [hv]
        unfold PiLF
        ring
    · unfold PiHF PiLF; ring


