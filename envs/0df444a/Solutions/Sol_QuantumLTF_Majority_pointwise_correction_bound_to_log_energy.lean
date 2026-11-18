-- Prove2me | solution 1 for QuantumLTF.Majority.pointwise_correction_bound_to_log_energy
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T17:40:12.749202+00:00
-- url     : https://prove2.me/submissions/9267a707-cb61-49de-92c0-098394438ded

import Mathlib
import Theorems.Thm_QuantumLTF_Majority_harmonic_kernel_log_bound

open QuantumLTF.Majority

theorem solution : ∃ H : ℝ, 0 < H ∧ ∀ r : ℕ, 3 ≤ r → ∀ D : ℝ, 0 ≤ D →
    ∀ e : Fin (r+1) → ℝ,
      (∀ t : Fin (r+1), e t ≤ D * (r : ℝ) /
        (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ))) →
      (∑ t : Fin (r+1), e t) ≤ D * H * Real.log r := by
  obtain ⟨H, hH, hkernel⟩ := harmonic_kernel_log_bound
  refine ⟨H, hH, ?_⟩
  intro r hr D hD e he
  calc
    (∑ t : Fin (r+1), e t) ≤
        ∑ t : Fin (r+1), D * (r : ℝ) /
          (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) :=
      Finset.sum_le_sum fun t _ => he t
    _ = D * (∑ t : Fin (r+1), (r : ℝ) /
          (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ D * (H * Real.log r) :=
      mul_le_mul_of_nonneg_left (hkernel r hr) hD
    _ = D * H * Real.log r := by ring
