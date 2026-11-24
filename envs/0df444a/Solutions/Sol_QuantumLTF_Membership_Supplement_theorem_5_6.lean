-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_5_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:24:58.992424+00:00
-- url     : https://prove2.me/submissions/d1981fbf-27e2-4083-9b51-5db7b477345e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QuantumLTF_Membership_Supplement_probMixed_pad_stability
import Theorems.Thm_QuantumLTF_Membership_Supplement_tomography_ideal_input_56

set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example QuantumLTF.Membership.Supplement

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ K' : ℕ,
      ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ K : ℕ, C * n / ε ^ 2 ≤ K → ∀ q : ℕ, c * (n : ℝ) ^ 2 / ε ^ 2 ≤ 2 ^ q →
      ∀ s : ℕ, n ≤ 2 ^ s →
        ∃ (e : ℕ) (cq : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) (K * s + e))
          (pp : Circuit gatesRev (K * s + e)) (ℓo fo : ℕ) (ov : Fin n → (Fin ℓo ↪ Fin (K * s + e))),
          Uncontrolled cq ∧ ForwardOnly cq ∧ cq.queryCount 0 ≤ 3 ∧
          (cq.gateCount : ℝ) ≤ C' * (n / ε ^ 2) * (1 + Real.log (1 / ε)) * Real.log n ^ K' ∧
          (pp.size : ℝ) ≤ C' * (n / ε) ^ K' ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ (ξ : ℝ) (ρ : Matrix (Qubits (K * s)) (Qubits (K * s)) ℂ), IsStateOnSpan n s K ρ →
            traceNorm (ρ - dirTensorPow s K w) / 2 ≤ ξ →
          ∀ U : Matrix (Qubits (n * q + 1)) (Qubits (n * q + 1)) ℂ, IsQEX (q := q) w U →
            open Classical in
            probMixed (pp.unitary * cq.unitary fun _ => U) (padDensity e ρ)
              (fun z =>
                let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp (ov i) fo z
                v ≠ 0 ∧ ‖‖v‖⁻¹ • v - w‖ ≤ ε) ≥ 73 / 96 - ξ := by
  classical
  obtain ⟨C, c, hC, hc, C', hC', K', h⟩ :=
    QuantumLTF.Membership.Supplement.tomography_ideal_input_56
  refine ⟨C, c, hC, hc, C', hC', K', ?_⟩
  intro n hn ε hε hε' K hK q hq s hs
  obtain ⟨e, cq, pp, ℓo, fo, ov, hunc, hfwd, hqueries, hgates, hpp, hideal⟩ :=
    h n hn ε hε hε' K hK q hq s hs
  refine ⟨e, cq, pp, ℓo, fo, ov, hunc, hfwd, hqueries, hgates, hpp, ?_⟩
  intro w hw ξ ρ hρ hξ U hU
  obtain ⟨hσ, htσ, hproc⟩ := hideal w hw
  obtain ⟨hM, hsuccess⟩ := hproc U hU
  let P := fun z : Qubits (K*s+e) =>
    let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => readFp (ov i) fo z
    v ≠ 0 ∧ ‖‖v‖⁻¹ • v - w‖ ≤ ε
  have hstable := QuantumLTF.Membership.Supplement.probMixed_pad_stability
    (pp.unitary * cq.unitary (fun _ => U)) hM ρ (dirTensorPow s K w)
    hρ.1.1 hσ (hρ.2.1.trans htσ.symm) P
  have hlow := (abs_le.mp hstable).1
  change probMixed _ _ P ≥ _
  change probMixed _ _ P ≥ (73/96:ℝ) at hsuccess
  linarith
