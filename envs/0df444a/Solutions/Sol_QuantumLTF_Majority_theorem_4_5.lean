-- Prove2me | solution 1 for QuantumLTF.Majority.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-16T17:56:13.755295+00:00
-- url     : https://prove2.me/submissions/a6755c19-8dbe-4640-8c9d-a813c2cf3213

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model
import Theorems.Thm_QuantumLTF_Majority_theorem_4_10_fixed_error

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
  obtain ⟨C, hC, hmain⟩ :=
    theorem_4_10_fixed_error (1 / 3) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro n k hk hkn
  obtain ⟨m, c, out, d, hlearn, hq, hg, hd⟩ :=
    hmain n k hk hkn
  refine ⟨m, c, out, hq, ?_⟩
  intro A hA hkA
  have h := hlearn A hA hkA
  norm_num at h ⊢
  linarith
