-- Prove2me | solution 1 for ReferralPriority.Optimal.relaxation_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:19:36.462527+00:00
-- url     : https://prove2.me/submissions/a20a0eac-5bec-47ff-a7a9-3e72aad3adf1

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

open ReferralPriority.Optimal

theorem solution (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (Lam : ℝ)
    (hL0 : 0 < Lam) :
    rSB E Lam ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ r α : ℝ, r ∈ Set.Ioc (0 : ℝ) 1 → α ∈ Set.Ioc (0 : ℝ) 1 → Stable E Lam r α →
        0 ≤ E.V - E.k / α - E.c / (E.mu * (1 - r * α) - Lam * r * α ^ 2) →
          throughput Lam r α ≤ throughput Lam (rSB E Lam) 1 := by
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  have hcm : 0 < E.c / E.mu := div_pos hc hmu
  set q := E.V - E.k with hq
  have ha : E.c < q * E.mu := by
    have : E.c / E.mu < q := by linarith
    rwa [div_lt_iff₀ hmu] at this
  have hq0 : 0 < q := by linarith
  have hV0 : 0 < E.V := by linarith
  have hML : 0 < E.mu + Lam := by linarith
  have h1r : 1 - rSB E Lam = (q * Lam + E.c) / (q * (E.mu + Lam)) := by
    unfold rSB; rw [← hq]; field_simp; ring
  have hden : 0 < q * Lam + E.c := by positivity
  have hrSB0 : 0 < rSB E Lam := by
    unfold rSB; rw [← hq]; apply div_pos (by linarith) (by positivity)
  have hrSB1 : rSB E Lam < 1 := by
    have : 0 < 1 - rSB E Lam := by rw [h1r]; positivity
    linarith
  refine ⟨⟨hrSB0, hrSB1⟩, ?_⟩
  rintro r α ⟨hr0, hr1⟩ ⟨hα0, hα1⟩ hst hA1
  unfold Stable at hst
  unfold throughput
  set x := r * α with hx
  have hx1 : x ≤ 1 := by rw [hx]; nlinarith
  have hx0 : 0 < x := mul_pos hr0 hα0
  set E1 := E.mu * (1 - x) - Lam * r * α ^ 2 with hE1
  have hE1' : E1 = E.mu * (1 - x) - Lam * α * x := by rw [hE1, hx]; ring
  have hLa : 0 < Lam * α := mul_pos hL0 hα0
  have hE1pos : 0 < E1 := by
    rw [hE1']; nlinarith [mul_le_mul_of_nonneg_left hx1 hLa.le]
  have hcE : 0 < E.c / E1 := div_pos hc hE1pos
  have hVa : E.V - E.k / α = (α * E.V - E.k) / α := by field_simp
  set p := α * E.V - E.k with hp
  have hp0 : 0 < p := by
    have : 0 < (α * E.V - E.k) / α := by rw [← hVa]; linarith
    exact (div_pos_iff_of_pos_right hα0).mp this
  have hpq : p ≤ q := by rw [hp, hq]; nlinarith
  -- c α ≤ p E1
  have hcp : E.c * α ≤ p * E1 := by
    have h2 : E.c / E1 ≤ p / α := by rw [← hVa]; linarith
    rw [div_le_div_iff₀ hE1pos hα0] at h2
    linarith
  set u := 1 - x with hu
  have hu0 : 0 < u := pos_of_mul_pos_right (by linarith : 0 < E.mu * u) hmu.le
  -- H : α (c + p Λ) ≤ u p (µ + Λ α)
  have H : α * (E.c + p * Lam) ≤ u * p * (E.mu + Lam * α) := by
    have : E1 = u * (E.mu + Lam * α) - Lam * α := by rw [hE1', hu]; ring
    rw [this] at hcp; nlinarith
  have hK : p * (E.mu + Lam * α) * (q * Lam + E.c) ≤ q * (E.mu + Lam) * (p * Lam + E.c) := by
    have e1 : p * (E.mu + Lam * α) ≤ p * (E.mu + Lam) := by
      apply mul_le_mul_of_nonneg_left _ hp0.le; nlinarith
    have e2 : p * (q * Lam + E.c) ≤ q * (p * Lam + E.c) := by nlinarith
    calc p * (E.mu + Lam * α) * (q * Lam + E.c) ≤ p * (E.mu + Lam) * (q * Lam + E.c) :=
          mul_le_mul_of_nonneg_right e1 hden.le
      _ = (E.mu + Lam) * (p * (q * Lam + E.c)) := by ring
      _ ≤ (E.mu + Lam) * (q * (p * Lam + E.c)) := mul_le_mul_of_nonneg_left e2 hML.le
      _ = q * (E.mu + Lam) * (p * Lam + E.c) := by ring
  have hPm : 0 < p * (E.mu + Lam * α) := by positivity
  have G : α * (q * Lam + E.c) ≤ q * (E.mu + Lam) * u := by
    have h4 : q * (E.mu + Lam) * (α * (E.c + p * Lam)) ≤ q * (E.mu + Lam) * (u * p * (E.mu + Lam * α)) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    have h5 := mul_le_mul_of_nonneg_left hK hα0.le
    have eq : p * (E.mu + Lam * α) * (q * (E.mu + Lam) * u - α * (q * Lam + E.c)) =
        q * (E.mu + Lam) * (u * p * (E.mu + Lam * α)) - α * (p * (E.mu + Lam * α) * (q * Lam + E.c)) := by ring
    have eq2 : q * (E.mu + Lam) * (α * (E.c + p * Lam)) = α * (q * (E.mu + Lam) * (p * Lam + E.c)) := by ring
    have h3 : 0 ≤ p * (E.mu + Lam * α) * (q * (E.mu + Lam) * u - α * (q * Lam + E.c)) := by
      rw [eq]; linarith
    have := (mul_nonneg_iff_of_pos_left hPm).mp h3
    linarith
  rw [mul_one, mul_one, h1r, div_div_eq_mul_div, div_le_div_iff₀ hu0 hden]
  have := mul_le_mul_of_nonneg_left G hL0.le
  calc Lam * α * (q * Lam + E.c) = Lam * (α * (q * Lam + E.c)) := by ring
    _ ≤ Lam * (q * (E.mu + Lam) * u) := this
    _ = Lam * (q * (E.mu + Lam)) * u := by ring
