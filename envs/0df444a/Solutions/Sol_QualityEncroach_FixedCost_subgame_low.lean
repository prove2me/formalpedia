-- Prove2me | solution 1 for QualityEncroach.FixedCost.subgame_low
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:32:57.653584+00:00
-- url     : https://prove2.me/submissions/69df0d7c-3a0c-4552-aa3c-c9eae152c00c

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Reduced

open QualityEncroach.FixedCost

namespace QE3Core

lemma stage3 (k c w u t q a : ℝ) (hu : 0 < u)
    (hpM : ∀ qM, QualityEncroach.Differ.priceM u t qM q = u * (1 - qM - a * q)) :
    ∀ x, 0 ≤ x → mfrPayoff k c ⟨w, u, t, q, x⟩ ≤
      mfrPayoff k c ⟨w, u, t, q, max 0 ((1 - a * q - c / u) / 2)⟩ := by
  set m := (1 - a * q - c / u) / 2 with hm
  have hcu : u * (c / u) = c := mul_div_cancel₀ c hu.ne'
  have hF : ∀ x, mfrPayoff k c ⟨w, u, t, q, x⟩ =
      w * q + (2 * u * m - u * x) * x - max (k * u ^ 2) (k * (t * u) ^ 2) := by
    intro x
    simp only [mfrPayoff, hpM, hm]
    linear_combination x * hcu
  intro x hx
  rw [hF, hF]
  rcases le_total 0 m with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (x - m)]
  · rw [max_eq_left h]
    nlinarith [mul_nonneg (mul_nonneg hu.le hx) (neg_nonneg.mpr h), mul_nonneg hu.le (sq_nonneg x)]

lemma stage2 (u t w q a γ c : ℝ) (hu : 0 < u)
    (hpR : ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - γ * qM)
    (hA : 0 < t * u - γ * a / 2) (hγ : 0 < γ)
    (hm : 0 < (1 - a * q - c / u) / 2)
    (hw : w = t * u - γ * (1 - c / u) / 2 - 2 * (t * u - γ * a / 2) * q) :
    ∀ x, 0 ≤ x →
      QualityEncroach.Differ.retailerPayoff ⟨w, u, t, x, max 0 ((1 - a * x - c / u) / 2)⟩ ≤
      QualityEncroach.Differ.retailerPayoff ⟨w, u, t, q, max 0 ((1 - a * q - c / u) / 2)⟩ := by
  intro x hx
  simp only [QualityEncroach.Differ.retailerPayoff, hpR]
  rw [max_eq_right hm.le]
  have hle : (t * u * (1 - x) - γ * max 0 ((1 - a * x - c / u) / 2) - w) * x ≤
      (t * u * (1 - x) - γ * ((1 - a * x - c / u) / 2) - w) * x := by
    have := le_max_right 0 ((1 - a * x - c / u) / 2)
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hγ.le hx)]
  rw [hw] at hle ⊢
  nlinarith [mul_nonneg hA.le (sq_nonneg (x - q))]

lemma payoff (k c u t w q a : ℝ) (hu : 0 < u)
    (hpM : ∀ qM, QualityEncroach.Differ.priceM u t qM q = u * (1 - qM - a * q))
    (hm : 0 < (1 - a * q - c / u) / 2) :
    mfrPayoff k c ⟨w, u, t, q, max 0 ((1 - a * q - c / u) / 2)⟩ =
      w * q + u * ((1 - a * q - c / u) / 2) ^ 2 - max (k * u ^ 2) (k * (t * u) ^ 2) := by
  rw [max_eq_right hm.le]
  simp only [mfrPayoff, hpM]
  have hu0 : u ≠ 0 := hu.ne'
  field_simp
  ring

end QE3Core

namespace QE3Branch

lemma lo_pM (u t : ℝ) (ht1 : 1 ≤ t) :
    ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - 1 * x) := by
  intro qM x; unfold QualityEncroach.Differ.priceM
  split_ifs with h
  · have : t = 1 := le_antisymm h ht1
    subst this; ring
  · ring

lemma lo_pR (u t : ℝ) (ht1 : 1 ≤ t) :
    ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - u * qM := by
  intro qM x; unfold QualityEncroach.Differ.priceR
  split_ifs with h
  · have : t = 1 := le_antisymm h ht1
    subst this; ring
  · ring

lemma lo_cost (k u t : ℝ) (hk : 0 < k) (ht1 : 1 ≤ t) :
    max (k * u ^ 2) (k * (t * u) ^ 2) = k * t ^ 2 * u ^ 2 := by
  rw [max_eq_right]
  · ring
  · have : u ^ 2 ≤ (t * u) ^ 2 := by
      have ht2 : 1 ≤ t ^ 2 := by nlinarith
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg u)]
    nlinarith

lemma lo_psi (c u t x : ℝ) (hu : 0 < u) (ht1 : 1 ≤ t) :
    (t * u - u * (1 - c / u) / 2 - 2 * (t * u - u * 1 / 2) * x) * x +
      u * ((1 - 1 * x - c / u) / 2) ^ 2 =
      ((4 * t ^ 2 - 1) * u / (4 * (8 * t - 5)) + (1 - 4 * t) * c / (2 * (8 * t - 5)) +
        (8 * t - 1) * c ^ 2 / (4 * (8 * t - 5) * u)) -
        (u * (8 * t - 5) / 4) * (x - (2 * c / ((8 * t - 5) * u) + 2 * (t - 1) / (8 * t - 5))) ^ 2 := by
  have h85 : 8 * t - 5 ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 * t - 5 = D at *
  field_simp
  have ht : t = (D + 5) / 8 := by linarith
  subst ht
  ring

lemma lo_m (c u t : ℝ) (hu : 0 < u) (ht1 : 1 ≤ t) :
    (1 - 1 * (2 * c / ((8 * t - 5) * u) + 2 * (t - 1) / (8 * t - 5)) - c / u) / 2 =
      ((6 * t - 3) * u - (8 * t - 3) * c) / (2 * (8 * t - 5) * u) := by
  have h85 : 8 * t - 5 ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 * t - 5 = D at *
  field_simp
  have ht : t = (D + 5) / 8 := by linarith
  subst ht
  ring

end QE3Branch


open QE3Core QE3Branch QualityEncroach.FixedCost in
theorem solution (k c t u : ℝ) (hk : 0 < k) (hc : 0 ≤ c)
    (ht : 1 ≤ t) (hu : (8 * t - 3) * c < (6 * t - 3) * u) :
    (∀ w qR qM : ℝ, 0 ≤ qR → 0 ≤ qM →
      mfrPayoff k c ⟨w, u, t, qR, qM⟩ ≤
        mfrPayoff k c ⟨w, u, t, qR, qMReplyLo c u qR⟩) ∧
    (∀ w : ℝ, 0 ≤ qRLoAt c w t u →
      0 < qMReplyLo c u (qRLoAt c w t u) →
      ∀ qR : ℝ, 0 ≤ qR →
        QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qR, qMReplyLo c u qR⟩ ≤
          QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qRLoAt c w t u,
            qMReplyLo c u (qRLoAt c w t u)⟩) ∧
    (∀ w : ℝ, 0 ≤ qRLoAt c w t u →
      0 < qMReplyLo c u (qRLoAt c w t u) →
      mfrPayoff k c ⟨w, u, t, qRLoAt c w t u,
        qMReplyLo c u (qRLoAt c w t u)⟩ ≤
        mfrPayoff k c ⟨wLo c t u, u, t, qRLo c t u, qMLo c t u⟩) ∧
    qRLoAt c (wLo c t u) t u = qRLo c t u ∧
    qMReplyLo c u (qRLo c t u) = qMLo c t u ∧
    0 < qMLo c t u ∧
    mfrPayoff k c ⟨wLo c t u, u, t, qRLo c t u, qMLo c t u⟩ =
      PiLo k c t u := by
  have ht0 : 0 < t := by linarith
  have h85 : 0 < 8 * t - 5 := by linarith
  have hupos : 0 < u := by
    by_contra hh; push Not at hh; nlinarith
  have hu0 : u ≠ 0 := hupos.ne'
  have h2t : 2 * t - 1 ≠ 0 := by intro h; linarith
  have hA : 0 < t * u - u * 1 / 2 := by nlinarith
  have hrep : ∀ x, qMReplyLo c u x = max 0 ((1 - 1 * x - c / u) / 2) := by
    intro x; unfold qMReplyLo; rw [one_mul]
  have hw : ∀ w, w = t * u - u * (1 - c / u) / 2 -
      2 * (t * u - u * 1 / 2) * qRLoAt c w t u := by
    intro w; unfold qRLoAt
    generalize hE : 2 * t - 1 = E at *
    field_simp
    have ht' : t = (E + 1) / 2 := by linarith
    subst ht'
    ring
  have hmLo : (1 - 1 * qRLo c t u - c / u) / 2 = qMLo c t u := by
    unfold qRLo qMLo
    have h85' : 8 * t - 5 ≠ 0 := h85.ne'
    generalize hD : 8 * t - 5 = D at *
    field_simp
    have ht : t = (D + 5) / 8 := by linarith
    subst ht
    ring
  have hqMLo : 0 < qMLo c t u := by
    rw [← hmLo]; unfold qRLo; rw [lo_m c u t hupos ht]
    apply div_pos _ (by positivity)
    linarith
  have h7 : mfrPayoff k c ⟨wLo c t u, u, t, qRLo c t u, qMLo c t u⟩ = PiLo k c t u := by
    simp only [mfrPayoff, lo_pM u t ht]
    rw [lo_cost k u t hk ht]
    unfold wLo qRLo qMLo PiLo
    have h85' : 8 * t - 5 ≠ 0 := h85.ne'
    generalize hD : 8 * t - 5 = D at *
    field_simp
    have ht : t = (D + 5) / 8 := by linarith
    subst ht
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hqMLo, h7⟩
  · intro w qR qM hqR hqM
    rw [hrep]
    exact stage3 k c w u t qR 1 hupos (fun qM => lo_pM u t ht qM qR) qM hqM
  · intro w h0 hpos qR hqR
    rw [hrep, hrep]
    rw [hrep] at hpos
    have hm : 0 < (1 - 1 * qRLoAt c w t u - c / u) / 2 := by
      rcases lt_max_iff.mp hpos with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    exact stage2 u t w _ 1 u c hupos (lo_pR u t ht) hA hupos hm (hw w) qR hqR
  · intro w h0 hpos
    rw [hrep] at hpos ⊢
    have hm : 0 < (1 - 1 * qRLoAt c w t u - c / u) / 2 := by
      rcases lt_max_iff.mp hpos with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    rw [h7, payoff k c u t w _ 1 hupos (fun qM => lo_pM u t ht qM _) hm,
      lo_cost k u t hk ht]
    have hpsi := lo_psi c u t (qRLoAt c w t u) hupos ht
    have e : w * qRLoAt c w t u = (t * u - u * (1 - c / u) / 2 -
        2 * (t * u - u * 1 / 2) * qRLoAt c w t u) * qRLoAt c w t u :=
      congrArg (· * qRLoAt c w t u) (hw w)
    have hα : 0 ≤ (u * (8 * t - 5) / 4) *
        (qRLoAt c w t u - (2 * c / ((8 * t - 5) * u) + 2 * (t - 1) / (8 * t - 5))) ^ 2 := by
      have : 0 ≤ u * (8 * t - 5) / 4 := by positivity
      positivity
    have ePi : PiLo k c t u = (4 * t ^ 2 - 1) * u / (4 * (8 * t - 5)) +
        (1 - 4 * t) * c / (2 * (8 * t - 5)) +
        (8 * t - 1) * c ^ 2 / (4 * (8 * t - 5) * u) - k * t ^ 2 * u ^ 2 := rfl
    linarith
  · unfold qRLoAt wLo qRLo
    have h85' : 8 * t - 5 ≠ 0 := h85.ne'
    generalize hD : 8 * t - 5 = D at *
    field_simp
    have ht : t = (D + 5) / 8 := by linarith
    subst ht
    ring
  · rw [hrep, hmLo, max_eq_right hqMLo.le]
