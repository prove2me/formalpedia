-- Prove2me | solution 1 for QuantumLTF.Majority.theorem_4_9_fixed_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T12:16:03.022996+00:00
-- url     : https://prove2.me/submissions/6492a0f1-b840-4855-8010-0f61f49b11e2

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

theorem compiler_section4_efficient : ∀ ε : ℝ, 0<ε → ε<1 →
    ∃ C : ℝ, 0<C ∧ ∀ n k : ℕ, 2≤k → k≤n →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m)
        (out : Fin n ↪ Fin m) (d : ℕ), LearnsUpTo (k:=k) c out (1-ε) ∧
        (c.queryCount 0 : ℝ)≤C*Real.log k ∧
        (c.gateCount : ℝ)≤C*n*Real.log (n+1)*Real.log k ∧
        (d:ℝ)≤C*Real.log (n+1)*Real.log k := by
  classical
  intro ε hε hε'
  obtain ⟨C, hC, h⟩ := Supplement.theorem_4_10 ε hε hε'
  refine ⟨C, hC, ?_⟩
  intro n k hk hn
  obtain ⟨m, c, out, hq, hg, hd, hc⟩ := h k n hk hn
  have hlog : Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+1) :=
    Real.log_le_log (by exact_mod_cast (show 0<n by omega)) (by linarith)
  have hlogk : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤k by omega))
  refine ⟨m, c, out, Supplement.nonOracleDepth c, ?_, hq, ?_, ?_⟩
  · intro A hA hAk
    simpa only [compiler_supplement_oracle_eq] using hc A ⟨Finset.card_pos.mpr hA, hAk⟩
  · exact hg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (by positivity)) hlogk)
  · exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog hC.le) hlogk)

theorem solution : ∀ ε : ℝ, 0<ε → ε<1 →
    ∃ C : ℝ, 0<C ∧ ∀ n k : ℕ, 2≤k → k≤n → Odd k →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m)
        (out : Fin n ↪ Fin m) (d : ℕ), LearnsExact (k:=k) c out (1-ε) ∧
        (c.queryCount 0 : ℝ)≤C*Real.log k ∧
        (c.gateCount : ℝ)≤C*n*Real.log (n+1)*Real.log k ∧
        (d:ℝ)≤C*Real.log (n+1)*Real.log k := by
  intro ε hε hε'
  obtain ⟨C, hC, h⟩ := compiler_section4_efficient ε hε hε'
  refine ⟨C, hC, ?_⟩
  intro n k hk hn _
  obtain ⟨m, c, out, d, hc, hq, hg, hd⟩ := h n k hk hn
  refine ⟨m, c, out, d, ?_, hq, hg, hd⟩
  intro A hA
  exact hc A (Finset.card_pos.mp (by omega)) (by omega)
