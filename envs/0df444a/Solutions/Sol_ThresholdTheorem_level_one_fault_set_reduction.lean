-- Prove2me | solution 1 for ThresholdTheorem.level_one_fault_set_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T21:22:32.016093+00:00
-- url     : https://prove2.me/submissions/f38280e4-d76f-40ce-a0ba-43c2eda7df16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic
import Definitions.Def_threshold_theorem_joint_faults
import Theorems.Thm_ThresholdTheorem_level_one_joint_fault_reduction
import Theorems.Thm_ThresholdTheorem_jointFaultyState_sequentialize

open ThresholdTheorem

theorem solution :
    ∃ (M : ℕ) (A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∃ (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
            (Φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ)),
            (∀ ℓ, (pairs ℓ).card ≤ M) ∧ (∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2) ∧
            (∀ (F S : Finset (ℕ × ℕ)), S ⊆ Φ F →
              ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ F) ∧
                ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂)) ∧
            ∀ m : ℕ, ∃ m' : ℕ, ∀ (F : Finset (ℕ × ℕ))
              (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)),
              ∃ fault' : ℕ → ℕ → (k : ℕ) → Channel (k + m'),
                pushDist (blockMap dec) (dataOutDist (faultyState F fault C')) =
                  dataOutDist (faultyState (Φ F) fault' C) := by
  obtain ⟨M, A, b, dec, h⟩ := level_one_joint_fault_reduction
  refine ⟨M, A, b, dec, ?_⟩
  intro Q _ _ C
  obtain ⟨C', hsize, pairs, Ψ, hcard, htwo, hwit, hrep⟩ := h Q C
  refine ⟨C', hsize, pairs, fun F => Ψ F ∪ predLocs C (Ψ F), hcard, htwo, hwit, ?_⟩
  intro m
  obtain ⟨m₁, hm₁⟩ := hrep m
  obtain ⟨m₂, hm₂⟩ := jointFaultyState_sequentialize C m₁
  refine ⟨m₂, fun F fault => ?_⟩
  obtain ⟨J, hJ, heq⟩ := hm₁ F fault
  obtain ⟨fault', hf⟩ := hm₂ (Ψ F) J hJ
  exact ⟨fault', heq.trans hf⟩

