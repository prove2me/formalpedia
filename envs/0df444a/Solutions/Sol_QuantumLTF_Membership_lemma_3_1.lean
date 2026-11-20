-- Prove2me | solution 1 for QuantumLTF.Membership.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T04:30:16.778628+00:00
-- url     : https://prove2.me/submissions/11d60bcb-3590-4507-94df-e23b5704fe41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_addrOf
import Theorems.Thm_QuantumLTF_Membership_uniform_dyadic_reference_direction

open QAlgorithms
open QuantumLTF.Membership

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ ℓ f : ℕ, f ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log n ∧ ∃ μ : PMF (Qubits (n * ℓ)),
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          (μ.toOuterMeasure {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧
            |inner ℝ w (addrOf n ℓ f z)| ≤ 3}).toReal ≥ 4 / 5 := by
  rcases uniform_dyadic_reference_direction with ⟨C, hC, hsampler⟩
  refine ⟨C, hC, ?_⟩
  intro n hn
  rcases hsampler n hn with ⟨ℓ, f, hf, hℓ, hprob⟩
  exact ⟨ℓ, f, hf, hℓ, PMF.uniformOfFintype (Qubits (n * ℓ)), hprob⟩
