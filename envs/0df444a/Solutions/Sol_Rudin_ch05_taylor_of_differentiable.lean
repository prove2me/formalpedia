-- Prove2me | solution 1 for Rudin.ch05_taylor_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T05:29:56.537965+00:00
-- url     : https://prove2.me/submissions/ad798f44-b0ea-43da-b671-a9243a45ff3d

import Mathlib

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinFix5

open Filter Topology

theorem ch05_taylor (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hlower : ∀ k < n - 1, ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlower hcont hderiv
  set s : Set ℝ := Set.uIcc α β with hs
  have hsub : s ⊆ Set.Icc a b := Set.uIcc_subset_Icc hα hβ
  have hmin : min α β < max α β := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have huniq : UniqueDiffOn ℝ s := by
    rw [hs, Set.uIcc]
    exact uniqueDiffOn_Icc hmin
  have hαs : α ∈ s := Set.left_mem_uIcc
  -- the within-derivatives on `s` are the genuine ones
  have hbridge : ∀ k, k ≤ m → Set.EqOn (iteratedDerivWithin k f s) (iteratedDeriv k f) s := by
    intro k
    induction k with
    | zero =>
      intro _ y _
      simp [iteratedDerivWithin_zero, iteratedDeriv_zero]
    | succ k ih =>
      intro hk y hy
      have hkm : k < m := by omega
      have hIH : Set.EqOn (iteratedDerivWithin k f s) (iteratedDeriv k f) s := ih (by omega)
      rw [iteratedDerivWithin_succ, derivWithin_congr hIH (hIH hy),
        (hlower k hkm y (hsub hy)).derivWithin (huniq y hy), iteratedDeriv_succ]
  -- continuity and differentiability of the within-derivatives
  have hcontOn : ∀ k, k ≤ m → ContinuousOn (iteratedDerivWithin k f s) s := by
    intro k hk
    refine ContinuousOn.congr ?_ (hbridge k hk)
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact hcont.mono hsub
    · exact fun y hy => ((hlower k hlt y (hsub hy)).continuousAt).continuousWithinAt
  have hdiffOn : ∀ k, k < m → DifferentiableOn ℝ (iteratedDerivWithin k f s) s := by
    intro k hk
    refine DifferentiableOn.congr ?_ (hbridge k hk.le)
    exact fun y hy => (hlower k hk y (hsub hy)).differentiableWithinAt
  have hcd : ContDiffOn ℝ (m : ℕ∞) f s := by
    refine contDiffOn_of_continuousOn_differentiableOn_deriv ?_ ?_
    · intro k hk
      exact hcontOn k (by exact_mod_cast hk)
    · intro k hk
      exact hdiffOn k (by exact_mod_cast hk)
  -- the top derivative on the open interval
  have hIooSub : Set.uIoo α β ⊆ Set.Ioo a b := by
    intro y hy
    rw [Set.uIoo, Set.mem_Ioo] at hy
    obtain ⟨h1, h2⟩ := hy
    refine ⟨lt_of_le_of_lt ?_ h1, lt_of_lt_of_le h2 ?_⟩
    · exact le_min hα.1 hβ.1
    · exact max_le hα.2 hβ.2
  have hIooSubS : Set.uIoo α β ⊆ s := by
    rw [hs, Set.uIcc, Set.uIoo]
    exact Set.Ioo_subset_Icc_self
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin m f s) (Set.uIoo α β) := by
    intro y hy
    refine DifferentiableWithinAt.congr ?_ (fun z hz => hbridge m le_rfl (hIooSubS hz))
      (hbridge m le_rfl (hIooSubS hy))
    exact (hderiv y (hIooSub hy)).differentiableWithinAt
  obtain ⟨x, hx, hEq⟩ := taylor_mean_remainder_lagrange hne hcd hf'
  refine ⟨x, ?_, ?_⟩
  · rw [Set.uIoo, Set.mem_Ioo] at hx
    obtain ⟨h1, h2⟩ := hx
    rcases lt_or_gt_of_ne hne with h | h
    · left
      rw [min_eq_left h.le] at h1
      rw [max_eq_right h.le] at h2
      exact ⟨h1, h2⟩
    · right
      rw [min_eq_right h.le] at h1
      rw [max_eq_left h.le] at h2
      exact ⟨h1, h2⟩
  · rw [taylor_within_apply] at hEq
    have hpoly : (∑ k ∈ Finset.range (m + 1),
          ((k.factorial : ℝ)⁻¹ * (β - α) ^ k) • iteratedDerivWithin k f s α)
        = ∑ k ∈ Finset.range (m + 1),
            iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hbridge k (by omega) hαs, smul_eq_mul]
      ring
    rw [hpoly] at hEq
    have htop : iteratedDerivWithin (m + 1) f s x = iteratedDeriv (m + 1) f x := by
      rw [iteratedDerivWithin_succ,
        derivWithin_congr (hbridge m le_rfl) (hbridge m le_rfl (hIooSubS hx)),
        (hderiv x (hIooSub hx)).derivWithin (huniq x (hIooSubS hx)), iteratedDeriv_succ]
    rw [htop] at hEq
    have hcomm : iteratedDeriv (m + 1) f x * (β - α) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℝ)
        = iteratedDeriv (m + 1) f x / (((m + 1).factorial : ℕ) : ℝ) * (β - α) ^ (m + 1) := by
      ring
    rw [hcomm] at hEq
    linarith

end RudinFix5

open Filter Topology in
theorem solution (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hlower : ∀ k < n - 1, ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (hcont : ContinuousOn (iteratedDeriv (n - 1) f) (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv (n - 1) f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n :=
  RudinFix5.ch05_taylor a b hab f n hn hlower hcont hderiv α β hα hβ hne
