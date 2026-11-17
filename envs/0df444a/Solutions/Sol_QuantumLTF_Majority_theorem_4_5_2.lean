-- Prove2me | solution 2 for QuantumLTF.Majority.theorem_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:15:06.812468+00:00
-- url     : https://prove2.me/submissions/2d8557a7-7be7-434f-ae21-dd0dde7abb2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_lemma_4_5
import Theorems.Thm_QuantumLTF_Majority_bounded_support_adversary_upper_bound

open QAlgorithms QuantumLTF.Membership
open QuantumLTF.Majority

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m)
        (out : Fin n ↪ Fin m),
        (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
        ∀ A : Finset (Fin n), A.Nonempty → A.card ≤ k →
          probEvent (act (c.unitary fun _ => majorityOracle A) (zeroKet m))
            (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3 := by
  obtain ⟨C₀, hC₀, hdual⟩ := lemma_4_5
  obtain ⟨C, hC, halg⟩ :=
    bounded_support_adversary_upper_bound C₀ hC₀ hdual
  refine ⟨C, hC, ?_⟩
  intro n k hk hkn
  obtain ⟨m, c, out, hq, hlearn⟩ := halg n k hk hkn
  exact ⟨m, c, out, hq, hlearn⟩

