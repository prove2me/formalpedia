-- Prove2me | solution 3 for QuantumLTF.Majority.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T12:16:01.51793+00:00
-- url     : https://prove2.me/submissions/eecf27da-7a99-4c2d-b758-62120756a178

import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity
import Definitions.Def_QuantumLTF_Sections45_Model
import Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_10

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Majority

theorem compiler_supplement_oracle_eq {n : ℕ} (A : Finset (Fin n)) :
    Supplement.majOracle A = majorityOracle A := by
  classical
  ext y z
  have hfilter : A ∩ (Finset.univ.filter fun i => Fin.init z i = true) =
      A.filter (fun i => Fin.init z i) := by
    ext i
    simp
  have hbit : decide (Supplement.majJunta A
      (Finset.univ.filter fun i => Fin.init z i = true) = -1) = majorityBit A (Fin.init z) := by
    unfold Supplement.majJunta majorityBit
    rw [hfilter]
    by_cases h : A.card ≤ 2 * (A.filter fun i => Fin.init z i).card
    · simp [h, Nat.not_lt.mpr h]
    · have hh : 2 * (A.filter fun i => Fin.init z i).card < A.card := by omega
      simp [h, hh]
  have heq : y = Fin.snoc (Fin.init z)
      (xor (z (Fin.last n)) (majorityBit A (Fin.init z))) ↔
      (∀ i : Fin n, y i.castSucc = z i.castSucc) ∧
        y (Fin.last n) = xor (z (Fin.last n)) (majorityBit A (Fin.init z)) := by
    constructor
    · intro h
      subst y
      simp [Fin.init]
    · rintro ⟨hi, hb⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hb
      · simpa [Fin.init] using hi j
  simp only [Supplement.majOracle, majorityOracle, Matrix.of_apply, hbit, heq]
  rfl

def compiler_widen_step {r m : ℕ} {a : Fin r → ℕ} :
    OracleStep gates12 a m → OracleStep {g : Gate | g.IsUnitary} a m
  | .gate g => .gate ⟨g.gate, g.mem.1, g.wires⟩
  | .query j adj ctrl wires hc => .query j adj ctrl wires hc

def compiler_widen_circuit {r m : ℕ} {a : Fin r → ℕ}
    (c : OracleCircuit gates12 a m) : OracleCircuit {g : Gate | g.IsUnitary} a m :=
  c.map compiler_widen_step

theorem compiler_widen_unitary {r m : ℕ} {a : Fin r → ℕ}
    (c : OracleCircuit gates12 a m)
    (orc : (j : Fin r) → Matrix (Qubits (a j)) (Qubits (a j)) ℂ) :
    (compiler_widen_circuit c).unitary orc = c.unitary orc := by
  have hstep (s : OracleStep gates12 a m) :
      OracleStep.mat orc (compiler_widen_step s) = OracleStep.mat orc s := by
    cases s with
    | gate g => rfl
    | query j adj ctrl wires hc => cases ctrl <;> rfl
  simp [compiler_widen_circuit, OracleCircuit.unitary, List.map_map, Function.comp_def, hstep]

theorem compiler_widen_count {r m : ℕ} {a : Fin r → ℕ}
    (c : OracleCircuit gates12 a m) (j : Fin r) :
    (compiler_widen_circuit c).queryCount j = c.queryCount j := by
  have hstep (s : OracleStep gates12 a m) :
      OracleStep.IsQueryTo j (compiler_widen_step s) = OracleStep.IsQueryTo j s := by
    cases s <;> rfl
  simp [compiler_widen_circuit, OracleCircuit.queryCount, List.countP_map, Function.comp_def, hstep]

theorem compiler_query_complexity_le {n m : ℕ}
    (P : Finset (Fin n) → Prop)
    (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m) (out : Fin n ↪ Fin m)
    (hc : ∀ A : Finset (Fin n), P A →
      probEvent (act (c.unitary fun _ => majorityOracle A) (zeroKet m))
        (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ (2/3:ℝ)) :
    Supplement.queryComplexity n P ≤ c.queryCount 0 := by
  classical
  apply Nat.sInf_le
  refine ⟨m, compiler_widen_circuit c, out, ?_, ?_⟩
  · simp [compiler_widen_count]
  · intro A hA
    simpa only [compiler_widen_unitary, compiler_supplement_oracle_eq] using hc A hA

set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Majority

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m)
        (out : Fin n ↪ Fin m),
        (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
        ∀ A : Finset (Fin n), A.Nonempty → A.card ≤ k →
          probEvent (act (c.unitary fun _ => majorityOracle A) (zeroKet m))
            (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3 := by
  classical
  obtain ⟨C, hC, h⟩ := Supplement.theorem_4_10 (1/3) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro n k hk hn
  obtain ⟨m, c, out, hq, _, _, hc⟩ := h k n hk hn
  refine ⟨m, c, out, hq, ?_⟩
  intro A hA hAk
  have hh := hc A ⟨Finset.card_pos.mpr hA, hAk⟩
  norm_num [compiler_supplement_oracle_eq] at hh
  exact hh
