-- Prove2me | solution 1 for QualityEncroach.FixedCost.subgame_high
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:31:52.415368+00:00
-- url     : https://prove2.me/submissions/cf199918-e6f9-4601-bcc2-eefab04b5c11

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

lemma hi_pM (u t : ℝ) (ht1 : t ≤ 1) :
    ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - t * x) := by
  intro qM x; unfold QualityEncroach.Differ.priceM; rw [if_pos ht1]

lemma hi_pR (u t : ℝ) (ht1 : t ≤ 1) :
    ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - (t * u) * qM := by
  intro qM x; unfold QualityEncroach.Differ.priceR; rw [if_pos ht1]; ring

lemma hi_cost (k u t : ℝ) (hk : 0 < k) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    max (k * u ^ 2) (k * (t * u) ^ 2) = k * u ^ 2 := by
  apply max_eq_left
  have : (t * u) ^ 2 ≤ u ^ 2 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg u)]
  nlinarith

lemma hi_psi (c u t x : ℝ) (hu : 0 < u) (ht1 : t ≤ 1) :
    (t * u - (t * u) * (1 - c / u) / 2 - 2 * (t * u - (t * u) * t / 2) * x) * x +
      u * ((1 - t * x - c / u) / 2) ^ 2 =
      (u + (8 - t) * c ^ 2 / ((8 - 5 * t) * u) - 2 * c) / 4 -
        (t * u * (8 - 5 * t) / 4) * (x - 2 * c / ((8 - 5 * t) * u)) ^ 2 := by
  have h85 : 8 - 5 * t ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 - 5 * t = D at *
  field_simp
  have ht : t = (8 - D) / 5 := by linarith
  subst ht
  ring

lemma hi_m (c u t : ℝ) (hu : 0 < u) (ht1 : t ≤ 1) :
    (1 - t * (2 * c / ((8 - 5 * t) * u)) - c / u) / 2 =
      ((8 - 5 * t) * u - (8 - 3 * t) * c) / (2 * (8 - 5 * t) * u) := by
  have h85 : 8 - 5 * t ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 - 5 * t = D at *
  field_simp
  have ht : t = (8 - D) / 5 := by linarith
  subst ht
  ring

end QE3Branch


open QE3Core QE3Branch QualityEncroach.FixedCost in
theorem solution (k c t u : ℝ) (hk : 0 < k) (hc : 0 ≤ c)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hu : (8 - 3 * t) * c / (8 - 5 * t) < u) :
    (∀ w qR qM : ℝ, 0 ≤ qR → 0 ≤ qM →
      mfrPayoff k c ⟨w, u, t, qR, qM⟩ ≤
        mfrPayoff k c ⟨w, u, t, qR, qMReplyHi c t u qR⟩) ∧
    (∀ w : ℝ, 0 ≤ qRHiAt c w t u →
      0 < qMReplyHi c t u (qRHiAt c w t u) →
      ∀ qR : ℝ, 0 ≤ qR →
        QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qR, qMReplyHi c t u qR⟩ ≤
          QualityEncroach.Differ.retailerPayoff ⟨w, u, t, qRHiAt c w t u,
            qMReplyHi c t u (qRHiAt c w t u)⟩) ∧
    (∀ w : ℝ, 0 ≤ qRHiAt c w t u →
      0 < qMReplyHi c t u (qRHiAt c w t u) →
      mfrPayoff k c ⟨w, u, t, qRHiAt c w t u,
        qMReplyHi c t u (qRHiAt c w t u)⟩ ≤
        mfrPayoff k c ⟨wHi c t u, u, t, qRHi c t u, qMHi c t u⟩) ∧
    qRHiAt c (wHi c t u) t u = qRHi c t u ∧
    qMReplyHi c t u (qRHi c t u) = qMHi c t u ∧
    0 < qMHi c t u ∧
    mfrPayoff k c ⟨wHi c t u, u, t, qRHi c t u, qMHi c t u⟩ =
      PiHi k c t u := by
  have h85 : 0 < 8 - 5 * t := by linarith
  have hupos : 0 < u := by
    have : 0 ≤ (8 - 3 * t) * c / (8 - 5 * t) := div_nonneg (by nlinarith) h85.le
    linarith
  have hu0 : u ≠ 0 := hupos.ne'
  have ht00 : t ≠ 0 := ht0.ne'
  have h2t : 2 - t ≠ 0 := by intro h; linarith
  have hA : 0 < t * u - (t * u) * t / 2 := by nlinarith [mul_pos ht0 hupos]
  have hγ : 0 < t * u := mul_pos ht0 hupos
  have hrep : ∀ x, qMReplyHi c t u x = max 0 ((1 - t * x - c / u) / 2) := fun x => rfl
  have hw : ∀ w, w = t * u - (t * u) * (1 - c / u) / 2 -
      2 * (t * u - (t * u) * t / 2) * qRHiAt c w t u := by
    intro w; unfold qRHiAt; field_simp; ring
  have hmHi : (1 - t * qRHi c t u - c / u) / 2 = qMHi c t u := by
    unfold qRHi qMHi
    have h85' : 8 - 5 * t ≠ 0 := h85.ne'
    generalize hD : 8 - 5 * t = D at *
    field_simp
    have ht : t = (8 - D) / 5 := by linarith
    subst ht
    ring
  have hqMHi : 0 < qMHi c t u := by
    rw [← hmHi]; unfold qRHi; rw [hi_m c u t hupos ht1]
    apply div_pos _ (by positivity)
    rw [div_lt_iff₀ h85] at hu; linarith
  have h7 : mfrPayoff k c ⟨wHi c t u, u, t, qRHi c t u, qMHi c t u⟩ = PiHi k c t u := by
    simp only [mfrPayoff, hi_pM u t ht1]
    rw [hi_cost k u t hk ht0 ht1]
    unfold wHi qRHi qMHi PiHi
    have h85' : 8 - 5 * t ≠ 0 := h85.ne'
    generalize hD : 8 - 5 * t = D at *
    field_simp
    have ht : t = (8 - D) / 5 := by linarith
    subst ht
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hqMHi, h7⟩
  · intro w qR qM hqR hqM
    rw [hrep]
    exact stage3 k c w u t qR t hupos (fun qM => hi_pM u t ht1 qM qR) qM hqM
  · intro w h0 hpos qR hqR
    rw [hrep, hrep]
    rw [hrep] at hpos
    have hm : 0 < (1 - t * qRHiAt c w t u - c / u) / 2 := by
      rcases lt_max_iff.mp hpos with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    exact stage2 u t w _ t (t * u) c hupos (hi_pR u t ht1) hA hγ hm (hw w) qR hqR
  · intro w h0 hpos
    rw [hrep] at hpos ⊢
    have hm : 0 < (1 - t * qRHiAt c w t u - c / u) / 2 := by
      rcases lt_max_iff.mp hpos with h | h
      · exact absurd h (lt_irrefl 0)
      · exact h
    rw [h7, payoff k c u t w _ t hupos (fun qM => hi_pM u t ht1 qM _) hm,
      hi_cost k u t hk ht0 ht1]
    have hpsi := hi_psi c u t (qRHiAt c w t u) hupos ht1
    have e : w * qRHiAt c w t u = (t * u - (t * u) * (1 - c / u) / 2 -
        2 * (t * u - (t * u) * t / 2) * qRHiAt c w t u) * qRHiAt c w t u :=
      congrArg (· * qRHiAt c w t u) (hw w)
    have hα : 0 ≤ (t * u * (8 - 5 * t) / 4) * (qRHiAt c w t u - 2 * c / ((8 - 5 * t) * u)) ^ 2 := by
      have : 0 ≤ t * u * (8 - 5 * t) / 4 := by positivity
      positivity
    unfold PiHi
    linarith
  · unfold qRHiAt wHi qRHi
    have h85' : 8 - 5 * t ≠ 0 := h85.ne'
    generalize hD : 8 - 5 * t = D at *
    field_simp
    have ht : t = (8 - D) / 5 := by linarith
    subst ht
    ring
  · rw [hrep, hmHi, max_eq_right hqMHi.le]
