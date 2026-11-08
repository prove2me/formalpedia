-- Prove2me | solution 1 for WagerFairDiv.toAlloc_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:40:41.759171+00:00
-- url     : https://prove2.me/submissions/c9da2bae-6bf2-4d88-963f-3a8bdfa79aa0

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : WagerFairDiv.Mech n m) (hB : WagerFairDiv.IsWagerMech B)
    (hBB : WagerFairDiv.WeaklyBB B)
    (hAB : WagerFairDiv.Corresponding A B) : WagerFairDiv.IsAllocMech A := by
  intro v e
  have htot : ∀ i0 : Fin n, 0 < e.total := fun i0 => by
    unfold WagerFairDiv.PosVec.total
    exact Finset.sum_pos (fun k _ => e.2 k) ⟨i0, Finset.mem_univ _⟩
  refine ⟨fun i j => ?_, fun j => ?_⟩
  · have hb := hB v e i j
    rw [hAB v e i j] at hb
    exact (mul_nonneg_iff_of_pos_left (htot i)).mp hb
  · rcases isEmpty_or_nonempty (Fin n) with h | ⟨⟨i0⟩⟩
    · simp
    · have h1 := hBB v e j
      simp_rw [hAB v e] at h1
      rw [← Finset.mul_sum] at h1
      exact (mul_le_iff_le_one_right (htot i0)).mp h1
