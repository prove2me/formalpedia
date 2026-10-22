-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.return_eq_flat_partial_returns
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:24:56.044353+00:00
-- url     : https://prove2.me/submissions/8d26aa7c-ccbc-45e9-9ab2-4a64dbed0037

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Returns

set_option autoImplicit false
open SuttonBartoRL.ImportanceSampling

theorem solution (R : ℕ → ℝ) (γ : ℝ) (t T : ℕ) (htT : t < T) :
    discountedReturn R γ t T =
      (1 - γ) * ∑ h ∈ Finset.Ioo t T, γ ^ (h - t - 1) * flatPartialReturn R t h +
        γ ^ (T - t - 1) * flatPartialReturn R t T := by
  obtain ⟨n, rfl⟩ : ∃ n, T = t + 1 + n := ⟨T - t - 1, by omega⟩
  clear htT
  induction n with
  | zero =>
    have : Finset.Ioo t (t + 1 + 0) = ∅ := by
      ext x; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    simp [discountedReturn, flatPartialReturn, this]
  | succ n ih =>
    have h1 : discountedReturn R γ t (t + 1 + (n + 1)) =
        discountedReturn R γ t (t + 1 + n) + γ ^ (n + 1) * R (t + 1 + n + 1) := by
      unfold discountedReturn
      rw [show t + 1 + (n + 1) = (t + 1 + n) + 1 by ring,
        Finset.sum_Ioc_succ_top (by omega)]
      rw [show t + 1 + n + 1 - t - 1 = n + 1 by omega]
    have h2 : ∀ k : ℕ, flatPartialReturn R t (t + 1 + k + 1) =
        flatPartialReturn R t (t + 1 + k) + R (t + 1 + k + 1) := by
      intro k
      unfold flatPartialReturn
      rw [Finset.sum_Ioc_succ_top (by omega)]
    have h3 : Finset.Ioo t (t + 1 + (n + 1)) = insert (t + 1 + n) (Finset.Ioo t (t + 1 + n)) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have h4 : t + 1 + n ∉ Finset.Ioo t (t + 1 + n) := by simp
    rw [h1, ih, h3, Finset.sum_insert h4, show t + 1 + (n + 1) = t + 1 + n + 1 by ring, h2 n]
    have e1 : t + 1 + n - t - 1 = n := by omega
    have e2 : t + 1 + n + 1 - t - 1 = n + 1 := by omega
    rw [e1, e2]
    ring
