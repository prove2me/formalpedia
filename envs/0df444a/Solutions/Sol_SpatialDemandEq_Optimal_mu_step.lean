-- Prove2me | solution 1 for SpatialDemandEq.Optimal.mu_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:33:05.671645+00:00
-- url     : https://prove2.me/submissions/9a9871af-28d0-4dd2-b2e9-f93cc2356acd

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

set_option autoImplicit false

open MeasureTheory SpatialDemandEq.Optimal

theorem solution {K : ℕ} (c lam B : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hB : lam < B)
    (a : Fin K → ℝ) (ha : ∀ k, 0 < a k) (hsum : ∑ k, a k = 1) :
    (∑ k, optRates lam B a k = B ∧ ∀ k, lam * a k < optRates lam B a k) ∧
      rateCost c lam (optRates lam B a) a = c / (B - lam) * (∑ k, Real.sqrt (a k)) ^ 2 ∧
      ∀ μ : Fin K → ℝ, ∑ k, μ k = B → (∀ k, lam * a k < μ k) → μ ≠ optRates lam B a →
        rateCost c lam (optRates lam B a) a < rateCost c lam μ a := by
  set S : ℝ := ∑ j, Real.sqrt (a j) with hS
  set T : ℝ := B - lam with hT
  have hTpos : 0 < T := by rw [hT]; linarith
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hsum
    · exact h
  have hSpos : 0 < S := by
    haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    exact Finset.sum_pos (fun j _ => Real.sqrt_pos.mpr (ha j)) Finset.univ_nonempty
  have hsq : ∀ k, Real.sqrt (a k) ^ 2 = a k := fun k => Real.sq_sqrt (ha k).le
  have hsqpos : ∀ k, 0 < Real.sqrt (a k) := fun k => Real.sqrt_pos.mpr (ha k)
  have hopt : ∀ k, optRates lam B a k - lam * a k = T * Real.sqrt (a k) / S := by
    intro k; simp only [optRates]; rw [← hS, ← hT]; try ring
  have hoptpos : ∀ k, 0 < T * Real.sqrt (a k) / S := fun k =>
    div_pos (mul_pos hTpos (hsqpos k)) hSpos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : ∑ k, optRates lam B a k = lam * ∑ k, a k + T * (∑ k, Real.sqrt (a k)) / S := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [optRates]; rw [← hS, ← hT]; try ring
    rw [this, hsum, ← hS]
    field_simp
    rw [hT]; ring
  · intro k; have := hopt k; have := hoptpos k; linarith
  · unfold rateCost
    have : ∀ k, a k * (c / (optRates lam B a k - lam * a k)) = c / T * S * Real.sqrt (a k) := by
      intro k
      rw [hopt k]
      have h1 := hsqpos k
      have e := hsq k
      generalize Real.sqrt (a k) = s at h1 e ⊢
      rw [← e]
      field_simp
    simp only [this]
    rw [← Finset.mul_sum, ← hS]; ring
  · intro μ hμ hμlt hne
    set x : Fin K → ℝ := fun k => μ k - lam * a k with hx
    have hxpos : ∀ k, 0 < x k := fun k => by simp only [hx]; linarith [hμlt k]
    have hxsum : ∑ k, x k = T := by
      simp only [hx]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hμ, hsum, hT]; ring
    have hrc : rateCost c lam μ a = c * ∑ k, a k / x k := by
      unfold rateCost; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hx]; ring
    have hrc0 : rateCost c lam (optRates lam B a) a = c * (S ^ 2 / T) := by
      unfold rateCost
      have : ∀ k, a k * (c / (optRates lam B a k - lam * a k)) = c / T * S * Real.sqrt (a k) := by
        intro k
        rw [hopt k]
        have h1 := hsqpos k
        have e := hsq k
        generalize Real.sqrt (a k) = s at h1 e ⊢
        rw [← e]
        field_simp
      simp only [this]
      rw [← Finset.mul_sum, ← hS]; field_simp
    set q : Fin K → ℝ := fun k => (Real.sqrt (a k) - S / T * x k) ^ 2 / x k with hq
    have hid : ∀ k, a k / x k = q k + 2 * (S / T) * Real.sqrt (a k) - (S / T) ^ 2 * x k := by
      intro k
      have h := (hxpos k).ne'
      simp only [hq]
      have e := hsq k
      generalize Real.sqrt (a k) = s at e ⊢
      rw [← e]
      field_simp
      ring
    have hsum2 : ∑ k, a k / x k = ∑ k, q k + S ^ 2 / T := by
      rw [Finset.sum_congr rfl (fun k _ => hid k), Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hS, hxsum]
      field_simp
      ring
    have hqnn : ∀ k, 0 ≤ q k := fun k => div_nonneg (sq_nonneg _) (hxpos k).le
    have hqpos : 0 < ∑ k, q k := by
      have : ∃ k, μ k ≠ optRates lam B a k := by
        by_contra h; push_neg at h; exact hne (funext h)
      obtain ⟨k, hk⟩ := this
      apply Finset.sum_pos' (fun k _ => hqnn k)
      refine ⟨k, Finset.mem_univ _, ?_⟩
      simp only [hq]
      apply div_pos _ (hxpos k)
      apply lt_of_le_of_ne (sq_nonneg _)
      intro h0
      have h1 : Real.sqrt (a k) - S / T * x k = 0 := by
        have := h0.symm; exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      apply hk
      have h2 : x k = T * Real.sqrt (a k) / S := by
        field_simp
        field_simp at h1
        linarith
      have := hopt k
      simp only [hx] at h2
      linarith
    rw [hrc, hrc0, hsum2]
    nlinarith
