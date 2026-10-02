-- Prove2me | solution 1 for ProcessingNetworks.TaskAllocation.subcriticality_iff_load_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:46:22.399289+00:00
-- url     : https://prove2.me/submissions/d27c5973-db49-43ae-aa85-4ab12bf6f874

import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel

open ProcessingNetworks.TaskAllocation in
theorem solution
    {L K : ℕ} (dat : TaskAllocationData L K) :
    IsSubcriticalGeneral dat ↔
      ∃ lam : Fin L → Fin K → ℝ, (∀ ℓ k, 0 ≤ lam ℓ k) ∧
        (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧ (∀ k, ∑ ℓ, dat.m ℓ k * lam ℓ k < 1) := by
  constructor
  · rintro ⟨lam, x, hlam, -, hsum, hx, hcap⟩
    refine ⟨lam, hlam, hsum, fun k => ?_⟩
    have h := hcap k
    simp only [hx] at h
    exact h
  · rintro ⟨lam, hlam, hsum, hcap⟩
    exact ⟨lam, fun ℓ k => dat.m ℓ k * lam ℓ k, hlam,
      fun ℓ k => mul_nonneg (le_of_lt (dat.hm ℓ k)) (hlam ℓ k), hsum, fun _ _ => rfl, hcap⟩
