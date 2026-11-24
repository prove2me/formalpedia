-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T17:58:36.789836+00:00
-- url     : https://prove2.me/submissions/ccc2d232-938f-4896-92f9-8c77f5deaf1e

import Theorems.Thm_QuantumLTF_Membership_theorem_3_4_assembly
import Theorems.Thm_QuantumLTF_Membership_lemma_2_1
import Theorems.Thm_QuantumLTF_Membership_lemma_3_1
import Theorems.Thm_QuantumLTF_Membership_lemma_3_2
import Theorems.Thm_QuantumLTF_Membership_theorem_3_1
import Theorems.Thm_QuantumLTF_Membership_theorem_3_2
import Theorems.Thm_QuantumLTF_Membership_lemma_3_3
import Theorems.Thm_QuantumLTF_Membership_theorem_3_3

open QAlgorithms QuantumLTF.Membership

theorem solution :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (ℓ f m ℓo fo : ℕ)
        (c : OracleCircuit gates12 (fun _ : Fin 1 => n * ℓ + 1) m)
        (oa : Fin n → (Fin ℓo ↪ Fin m)) (ob : Fin ℓo ↪ Fin m),
        Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * Real.log (n / ε) ∧
        (c.gateCount : ℝ) ≤ C * n * (Real.log (n / ε)) ^ K ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          probEvent (act (c.unitary fun _ => memOracle n ℓ f w θ) (zeroKet m))
            (fun z => disagree
              (ltf (WithLp.toLp 2 fun i => readFp (oa i) fo z) (readFp ob fo z))
              (ltf w θ) ≤ ε) ≥ 2 / 3 := by
  exact theorem_3_4_assembly
