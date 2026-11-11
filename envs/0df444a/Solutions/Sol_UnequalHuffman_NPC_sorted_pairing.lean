-- Prove2me | solution 1 for UnequalHuffman.NPC.sorted_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:28.248741+00:00
-- url     : https://prove2.me/submissions/ea51c79c-d657-4238-baa8-741e6a7cd721

import Mathlib

/-- §2.2, "Why the coefficient rows are nonincreasing" (p. 10): for nonincreasing coefficients
`u₁ ≥ ⋯ ≥ u_m` and coordinates `z`, the sorted pairing (the `k`-th largest coefficient with the
`k`-th smallest coordinate, i.e. `z ∘ π` nondecreasing) minimizes `∑_k u_k · z_{σ(k)}` over all
assignments `σ`, with signed coefficients and repeated coordinates allowed. -/
theorem solution {m : ℕ} (u : Fin m → ℤ) (hu : Antitone u) (z : Fin m → ℤ)
    (π σ : Equiv.Perm (Fin m)) (hπ : Monotone (z ∘ π)) :
    ∑ k, u k * z (π k) ≤ ∑ k, u k * z (σ k) := by
  have hmv : Monovary (fun k => -u k) (z ∘ π) := by
    intro i j hij
    have hji : ¬ j ≤ i := fun h => absurd (hπ h) (not_le.mpr hij)
    have : i ≤ j := (not_le.mp hji).le
    simpa using hu this
  have h := hmv.sum_smul_comp_perm_le_sum_smul (σ := σ.trans π.symm)
  simp only [smul_eq_mul, Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    neg_mul, Finset.sum_neg_distrib] at h
  linarith
