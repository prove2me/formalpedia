-- Prove2me | solution 1 for SplitPMSGame.core_properties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:37:45.790556+00:00
-- url     : https://prove2.me/submissions/3904bd02-55af-4e3b-ba61-861e9eb2aa52

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc

open Pointwise

open SplitPMSGame in
theorem solution {M : Type*} [Fintype M] (G₁ G₂ : Finset M → ℝ) :
    (∀ α : ℝ, 0 < α → SplitPMSGame.coreSet (α • G₁) = α • SplitPMSGame.coreSet G₁) ∧
      SplitPMSGame.coreSet G₁ + SplitPMSGame.coreSet G₂ ⊆ SplitPMSGame.coreSet (G₁ + G₂) := by
  constructor
  · intro α ha
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    simp only [SplitPMSGame.coreSet, Set.mem_setOf_eq, SplitPMSGame.IsCoreAlloc, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum, inv_mul_eq_iff_eq_mul₀ ha.ne', inv_mul_le_iff₀ ha]
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    simp only [SplitPMSGame.coreSet, Set.mem_setOf_eq, SplitPMSGame.IsCoreAlloc] at ha hb ⊢
    refine ⟨?_, fun T hT => ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, ha.1, hb.1]
    · simp only [Pi.add_apply, Finset.sum_add_distrib]
      linarith [ha.2 T hT, hb.2 T hT]
