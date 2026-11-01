-- Prove2me | solution 1 for ReferralPriority.Optimal.eq_A6_strict
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:25:46.939054+00:00
-- url     : https://prove2.me/submissions/9563c333-ad50-4337-a788-b7a487561244

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

open ReferralPriority.Optimal

theorem solution (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (rs : ℝ)
    (hrs : rs ∈ Set.Ioo (0 : ℝ) 1) (hg : gcubic E rs = 0) (Lam : ℝ) (hL0 : 0 < Lam)
    (hL : Lam < Lstar E rs) :
    0 < E.mu * (1 - rSB E Lam) - Lam ∧
      0 < E.V - rSB E Lam * E.k - E.c / (E.mu * (1 - rSB E Lam) - Lam) := by
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  obtain ⟨hrs0, hrs1⟩ := hrs
  have hcm : 0 < E.c / E.mu := div_pos hc hmu
  set q := E.V - E.k with hq
  have ha : E.c < q * E.mu := by
    have : E.c / E.mu < q := by linarith
    rwa [div_lt_iff₀ hmu] at this
  have hq0 : 0 < q := by linarith
  have hw : 0 < E.V - rs * E.k := by nlinarith
  -- the relation defining r* at Λ*
  have hstar : (E.mu * (1 - rs) - Lstar E rs * rs) * q = E.c := by
    unfold Lstar
    unfold gcubic at hg
    rw [← hq] at hg
    have hw' := hw.ne'
    field_simp
    linear_combination hg
  set r := rSB E Lam with hr_def
  have hML : 0 < E.mu + Lam := by linarith
  have hsb : (E.mu * (1 - r) - Lam * r) * q = E.c := by
    rw [hr_def]; unfold rSB; rw [← hq]
    field_simp
    ring
  have h1r : 0 < 1 - r := by
    have : (1 - r) * (q * (E.mu + Lam)) = q * Lam + E.c := by
      rw [hr_def]; unfold rSB; rw [← hq]; field_simp; ring
    have hp : 0 < q * Lam + E.c := by positivity
    rw [← this] at hp
    exact pos_of_mul_pos_left hp (by positivity)
  -- r > rs
  have hrr : rs < r := by
    have e : r * (E.mu + Lam) = rs * (E.mu + Lstar E rs) := by
      have := hsb.trans hstar.symm
      have := mul_right_cancel₀ hq0.ne' this
      linarith
    have : rs * (E.mu + Lam) < r * (E.mu + Lam) := by
      rw [e]; exact mul_lt_mul_of_pos_left (by linarith) hrs0
    exact lt_of_mul_lt_mul_right this hML.le
  have hr0 : 0 < r := by linarith
  -- h(r) < 0, where g = (1 - r) h
  set h : ℝ → ℝ := fun x => q * E.mu * ((1 - x) * (E.V - x * E.k)) - E.c * E.V with hh
  have hgh : ∀ x, gcubic E x = (1 - x) * h x := by
    intro x; simp only [gcubic, hh, hq]; ring
  have hhrs : h rs = 0 := by
    rw [hgh] at hg
    rcases mul_eq_zero.mp hg with h' | h'
    · linarith
    · exact h'
  have hhr : h r < 0 := by
    have e : h r - h rs = -(q * E.mu) * ((r - rs) * (q + E.k * (2 - r - rs))) := by
      simp only [hh, hq]; ring
    have p1 : 0 < (r - rs) * (q + E.k * (2 - r - rs)) := by
      apply mul_pos (by linarith)
      have : 0 ≤ E.k * (2 - r - rs) := mul_nonneg hkpos.le (by linarith)
      linarith
    have p2 : 0 < q * E.mu * ((r - rs) * (q + E.k * (2 - r - rs))) := by positivity
    linarith
  have hgr : gcubic E r < 0 := by rw [hgh]; exact mul_neg_of_pos_of_neg h1r hhr
  have hvr : 0 < E.V - r * E.k := by nlinarith
  -- N = c - q µ (1 - r)^2 > 0
  have hgr' : (E.V - r * E.k) * (E.c - q * E.mu * (1 - r) ^ 2) - E.c * q * r = - gcubic E r := by
    simp only [gcubic, hq]; ring
  have hN : 0 < E.c - q * E.mu * (1 - r) ^ 2 := by
    have h1 : E.c * q * r < (E.V - r * E.k) * (E.c - q * E.mu * (1 - r) ^ 2) := by linarith
    have h2 : 0 < E.c * q * r := by positivity
    exact pos_of_mul_pos_right (by linarith) hvr.le
  -- D_SB * (q r) = N
  have hDN : (E.mu * (1 - r) - Lam) * (q * r) = E.c - q * E.mu * (1 - r) ^ 2 := by
    linear_combination hsb
  have hqr : 0 < q * r := mul_pos hq0 hr0
  have hD : 0 < E.mu * (1 - r) - Lam := by
    have : 0 < (E.mu * (1 - r) - Lam) * (q * r) := by rw [hDN]; exact hN
    exact pos_of_mul_pos_left this hqr.le
  refine ⟨hD, ?_⟩
  have : E.c / (E.mu * (1 - r) - Lam) < E.V - r * E.k := by
    rw [div_lt_iff₀ hD]
    have h1 : E.c * (q * r) < (E.V - r * E.k) * ((E.mu * (1 - r) - Lam) * (q * r)) := by
      rw [hDN]; linarith
    have h2 : E.c * (q * r) < ((E.V - r * E.k) * (E.mu * (1 - r) - Lam)) * (q * r) := by linarith
    exact lt_of_mul_lt_mul_right h2 hqr.le
  linarith
