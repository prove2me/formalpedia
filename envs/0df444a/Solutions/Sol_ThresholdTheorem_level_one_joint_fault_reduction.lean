-- Prove2me | solution 1 for ThresholdTheorem.level_one_joint_fault_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:17:45.182763+00:00
-- url     : https://prove2.me/submissions/68bbadd5-361e-42d7-8603-ba296370ab02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_joint_faults
import Theorems.Thm_ThresholdTheorem_exRec_disjoint_pair_matching
import Theorems.Thm_ThresholdTheorem_level_one_exRec_joint_fault_simulation

set_option autoImplicit false
open ThresholdTheorem

theorem solution :
    ∃ (M : ℕ) (A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∃ (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
            (Ψ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ)),
            (∀ ℓ, (pairs ℓ).card ≤ M) ∧ (∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2) ∧
            (∀ (F S : Finset (ℕ × ℕ)), S ⊆ Ψ F ∪ predLocs C (Ψ F) →
              ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ F) ∧
                ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂)) ∧
            ∀ m : ℕ, ∃ m' : ℕ, ∀ (F : Finset (ℕ × ℕ))
              (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)),
              ∃ J : ℕ → JointFault Q m',
                (∀ t i, (J t).supp i ∈ badQubits C (Ψ F) t) ∧
                pushDist (blockMap dec) (dataOutDist (faultyState F fault C')) =
                  dataOutDist (jointFaultyState (Ψ F) J C) := by
  obtain ⟨R_max, A, b, dec, hsim⟩ := level_one_exRec_joint_fault_simulation
  refine ⟨(3 * R_max).choose 2, A, b, dec, fun Q _ _ C => ?_⟩
  obtain ⟨C', hsize, exRec, Ψ, hcard, hoverlap, hbad, hjoint⟩ := hsim Q C
  obtain ⟨pairs, hp_card, hp_two, hp_match⟩ :=
    exRec_disjoint_pair_matching R_max C exRec Ψ hcard hoverlap hbad
  exact ⟨C', hsize, pairs, Ψ, hp_card, hp_two, hp_match, hjoint⟩
