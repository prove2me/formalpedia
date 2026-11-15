-- Prove2me | solution 1 for QuantumLTF.Membership.uniform_dyadic_reference_direction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T04:33:04.577292+00:00
-- url     : https://prove2.me/submissions/7bed3191-387c-44af-aa69-f7ad3dc3b658
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_addrOf
import Theorems.Thm_QuantumLTF_Membership_uniform_dyadic_window
import Theorems.Thm_QuantumLTF_Membership_ceil_logb_bits_bound

open QAlgorithms
open QuantumLTF.Membership

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ ℓ f : ℕ, f ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log n ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ((PMF.uniformOfFintype (Qubits (n * ℓ))).toOuterMeasure
            {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧
              |inner ℝ w (addrOf n ℓ f z)| ≤ 3}).toReal ≥ 4 / 5 := by
  rcases ceil_logb_bits_bound with ⟨C, hC, hbits⟩
  refine ⟨C, hC, ?_⟩
  intro n hn
  rcases uniform_dyadic_window n hn with ⟨ℓ, f, hf, hℓ, hprob⟩
  refine ⟨ℓ, f, hf, ?_, hprob⟩
  exact le_trans (by exact_mod_cast hℓ) (hbits n hn)
