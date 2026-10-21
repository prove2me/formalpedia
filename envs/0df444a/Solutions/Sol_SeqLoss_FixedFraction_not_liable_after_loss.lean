-- Prove2me | solution 1 for SeqLoss.FixedFraction.not_liable_after_loss
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:01:02.226381+00:00
-- url     : https://prove2.me/submissions/7dfdc8d4-339c-4db1-beec-29aa50462381

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (hφ : IsRule φ) (hzt : ZeroTruncation φ) (n : ℕ) (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ)
    (h i : Fin n) (hhi : h < i) (hsingle : ∀ j, j ≠ h → ℓ j = 0) :
    φ n ℓ i = 0 := by
  obtain ⟨hnn, hpre, htot⟩ := (hφ n ℓ hℓ).1
  have hlt : h.val + 1 < n := by
    have := hhi; rw [Fin.lt_def] at this; have := i.isLt; omega
  have hp := hpre h.val hlt
  have hL : ∑ j, ℓ j = ℓ h := by
    rw [Finset.sum_eq_single h]
    · intro j _ hj; exact hsingle j hj
    · intro hh; exact absurd (Finset.mem_univ h) hh
  have hpre' : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ h.val), ℓ j = ℓ h := by
    rw [Finset.sum_eq_single h]
    · intro j _ hj; exact hsingle j hj
    · intro hh; exact absurd (by simp) hh
  rw [hpre'] at hp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val ≤ h.val)] at htot
  rw [hL] at htot
  have hrest : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ h.val), φ n ℓ j ≤ 0 := by linarith
  have hi' : i ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val ≤ h.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hhi
  have := Finset.single_le_sum (f := φ n ℓ) (fun j _ => hnn j) hi'
  linarith [hnn i]
