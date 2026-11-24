-- Prove2me | solution 1 for QuantumLTF.Majority.bounded_support_adversary_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:24:38.435324+00:00
-- url     : https://prove2.me/submissions/da138eeb-2782-4dde-843b-ffbcace44c64

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Majority_oracle
import Definitions.Def_QuantumLTF_Sections45_Model
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_compile_bounded_support_dual

open QAlgorithms QuantumLTF.Membership
open QuantumLTF.Majority

theorem solution : ∀ C₀ : ℝ, 0 < C₀ →
    (∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ,
        DualFeasible (fun A : BoundedSupports n k => A.1) X ∧
        DualCostAtMost X (C₀ * Real.log k)) →
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m)
        (out : Fin n ↪ Fin m),
        (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
        LearnsUpTo (k:=k) c out (2/3) := by
  intro C₀ hC₀ hdual
  obtain ⟨K, hK, hcompile⟩ := compile_bounded_support_dual
  let C : ℝ := K * (C₀ + (Real.log 2)⁻¹)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n k hk hkn
  obtain ⟨X, hfeas, hcost⟩ := hdual n k hk hkn
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  obtain ⟨m, c, out, hq, hlearn⟩ :=
    hcompile n k hk hkn (C₀ * Real.log k) (mul_nonneg (le_of_lt hC₀) hlogk)
      X hfeas hcost
  refine ⟨m, c, out, ?_, hlearn⟩
  have h2k : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog_le : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) h2k
  have hone : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log k := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hlog2).2 (by simpa using hlog_le)
  have hKone := mul_le_mul_of_nonneg_left hone (le_of_lt hK)
  dsimp [C]
  calc
    (c.queryCount 0 : ℝ) ≤ K * (C₀ * Real.log k + 1) := hq
    _ ≤ K * (C₀ + (Real.log 2)⁻¹) * Real.log k := by
      nlinarith

