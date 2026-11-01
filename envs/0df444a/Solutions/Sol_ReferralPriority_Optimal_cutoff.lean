-- Prove2me | solution 1 for ReferralPriority.Optimal.cutoff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:27:31.448364+00:00
-- url     : https://prove2.me/submissions/2e8aee7f-3f02-4505-b6aa-11df781d07e0

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model
import Theorems.Thm_ReferralPriority_Optimal_rFB_solves_A2
import Theorems.Thm_ReferralPriority_Optimal_gcubic_unique_root

open ReferralPriority.Optimal

theorem solution (E : Env) (hS : E.Standing) (hk : E.k < E.V - E.c / E.mu) (rs : ℝ)
    (hrs : rs ∈ Set.Ioo (0 : ℝ) 1) (hg : gcubic E rs = 0) :
    0 < Lstar E rs ∧ Lstar E rs < E.mu - E.c / E.V ∧ rFB E (Lstar E rs) = rs ∧
      ∀ Lam : ℝ, 0 < Lam → Lam < E.mu - E.c / E.V →
        ((1 / (E.mu * (1 - rFB E Lam) - Lam * rFB E Lam) ≤ W1pp E Lam ↔ Lstar E rs ≤ Lam) ∧
          (1 / (E.mu * (1 - rFB E Lam) - Lam * rFB E Lam) = W1pp E Lam ↔ Lam = Lstar E rs)) := by
  have hS' := hS
  obtain ⟨rs', hrs', -, huniq, hpos, hneg⟩ := gcubic_unique_root E hS hk
  have hrs_eq : rs = rs' := huniq rs hrs hg
  subst hrs_eq
  obtain ⟨hmu, hc, hkpos, hV⟩ := hS
  obtain ⟨hrs0, hrs1⟩ := hrs
  have hcm : 0 < E.c / E.mu := div_pos hc hmu
  set q := E.V - E.k with hq
  have hq0 : 0 < q := by linarith
  have hV0 : 0 < E.V := by linarith
  have hVx : ∀ x : ℝ, x ≤ 1 → 0 < E.V - x * E.k := by
    intro x hx; nlinarith
  -- the curve Λ = L(r) from (A.2)
  set L : ℝ → ℝ := fun x => E.mu * (1 - x) - E.c / (E.V - x * E.k) with hL
  have hLstar : Lstar E rs = L rs := rfl
  have hanti : StrictAntiOn L (Set.Icc 0 1) := by
    intro x hx y hy hxy
    simp only [hL]
    have hx' := hVx x hx.2
    have hy' := hVx y hy.2
    have h1 : E.c / (E.V - x * E.k) < E.c / (E.V - y * E.k) := by
      apply div_lt_div_of_pos_left hc hy'
      nlinarith
    nlinarith
  have hL0 : L 0 = E.mu - E.c / E.V := by simp [hL]
  -- h(rs) = 0, i.e. q µ (1 - rs)(V - rs k) = c V
  have hh : q * E.mu * ((1 - rs) * (E.V - rs * E.k)) = E.c * E.V := by
    have e : gcubic E rs = (1 - rs) * (q * E.mu * ((1 - rs) * (E.V - rs * E.k)) - E.c * E.V) := by
      simp only [gcubic, hq]; ring
    rw [e] at hg
    rcases mul_eq_zero.mp hg with h' | h'
    · linarith
    · linarith
  have hLpos : 0 < Lstar E rs := by
    rw [hLstar]; simp only [hL]
    have hw := hVx rs hrs1.le
    rw [sub_pos, div_lt_iff₀ hw]
    have : q * (E.mu * (1 - rs) * (E.V - rs * E.k)) = E.c * E.V := by rw [← hh]; ring
    have h2 : E.c * q < E.c * E.V := by
      apply mul_lt_mul_of_pos_left _ hc; linarith
    nlinarith
  have hLlt : Lstar E rs < E.mu - E.c / E.V := by
    rw [hLstar, ← hL0]
    exact hanti ⟨le_rfl, zero_le_one⟩ ⟨hrs0.le, hrs1.le⟩ hrs0
  -- for every admissible Λ, Λ = L(r^FB)
  have hLam : ∀ Lam : ℝ, 0 < Lam → Lam < E.mu - E.c / E.V →
      0 < rFB E Lam ∧ rFB E Lam < 1 ∧ Lam = L (rFB E Lam) := by
    intro Lam h0 h1
    obtain ⟨a, b, hD, hA2⟩ := rFB_solves_A2 E hS' Lam h0 h1
    refine ⟨a, b, ?_⟩
    simp only [hL]
    have hw := hVx _ b.le
    have : E.c / (E.mu * (1 - rFB E Lam) - Lam) = E.V - rFB E Lam * E.k := by linarith
    have : E.c / (E.V - rFB E Lam * E.k) = E.mu * (1 - rFB E Lam) - Lam := by
      rw [← this]; field_simp
    linarith
  have hrsI : rs ∈ Set.Icc (0 : ℝ) 1 := ⟨hrs0.le, hrs1.le⟩
  refine ⟨hLpos, hLlt, ?_, ?_⟩
  · obtain ⟨a, b, e⟩ := hLam _ hLpos hLlt
    rw [hLstar] at e
    exact hanti.injOn ⟨a.le, b.le⟩ hrsI e.symm
  · intro Lam h0 h1
    obtain ⟨a, b, hD, hA2⟩ := rFB_solves_A2 E hS' Lam h0 h1
    obtain ⟨-, -, hLx⟩ := hLam Lam h0 h1
    set x := rFB E Lam with hx
    have hw := hVx x b.le
    set D := E.mu * (1 - x) - Lam with hD_def
    have hcD : E.c / D = E.V - x * E.k := by linarith
    have hW1 : W1pp E Lam = q / E.c := by
      show 1 / D - E.k * (1 - x) / E.c = q / E.c
      have : 1 / D = (E.V - x * E.k) / E.c := by
        rw [← hcD]; field_simp
      rw [this, hq]; field_simp; ring
    set E2 := E.mu * (1 - x) - Lam * x with hE2
    have hE2pos : 0 < E2 := by
      have : D ≤ E2 := by rw [hD_def, hE2]; nlinarith
      linarith
    -- (V - x k)(q E2 - c) = g(x)
    have hLam' : Lam * (E.V - x * E.k) = E.mu * (1 - x) * (E.V - x * E.k) - E.c := by
      have : E.c = D * (E.V - x * E.k) := by rw [← hcD]; field_simp
      rw [this, hD_def]; ring
    have hgx : (E.V - x * E.k) * (q * E2 - E.c) = gcubic E x := by
      simp only [gcubic, hE2, hq]
      linear_combination (-(E.V - E.k) * x) * hLam'
    -- A3 ⟺ 0 ≤ g(x), equality ⟺ g(x) = 0
    have hA3 : 1 / E2 ≤ W1pp E Lam ↔ 0 ≤ gcubic E x := by
      rw [hW1, div_le_div_iff₀ hE2pos hc, ← hgx]
      constructor
      · intro h; apply mul_nonneg hw.le; linarith
      · intro h
        have := (mul_nonneg_iff_of_pos_left hw).mp h
        linarith
    have hA3e : 1 / E2 = W1pp E Lam ↔ gcubic E x = 0 := by
      rw [hW1, div_eq_div_iff hE2pos.ne' hc.ne', ← hgx]
      constructor
      · intro h; rw [show q * E2 - E.c = 0 by linarith, mul_zero]
      · intro h
        rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · linarith
    -- sign of g(x) versus x ≤ rs
    have hgle : 0 ≤ gcubic E x ↔ x ≤ rs := by
      constructor
      · intro h; by_contra hn; push Not at hn
        have := hneg x ⟨hn, b⟩; linarith
      · intro h
        rcases h.lt_or_eq with h' | h'
        · exact (hpos x ⟨a, h'⟩).le
        · rw [h']; exact le_of_eq hg.symm
    have hgeq : gcubic E x = 0 ↔ x = rs := by
      constructor
      · intro h; exact huniq x ⟨a, b⟩ h
      · intro h; rw [h]; exact hg
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨a.le, b.le⟩
    refine ⟨?_, ?_⟩
    · rw [hA3, hgle, hLstar, hLx]
      exact (hanti.le_iff_ge hrsI hxI).symm
    · rw [hA3e, hgeq, hLstar, hLx]
      exact ⟨fun h => by rw [h], fun h => hanti.injOn hxI hrsI h⟩
