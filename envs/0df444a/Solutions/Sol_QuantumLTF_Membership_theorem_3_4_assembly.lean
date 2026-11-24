-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_4_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:32.371246+00:00
-- url     : https://prove2.me/submissions/5ecbe681-326b-4c42-8520-5a459a74921c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_LearningCertificate
import Theorems.Thm_QuantumLTF_Membership_learningCertificate_circuit
import Theorems.Thm_QuantumLTF_Membership_learningCertificate_disagree

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
  obtain ⟨C, K, hC, h⟩ := learningCertificate_circuit
  refine ⟨C, K, hC, ?_⟩
  intro n hn ε hε hε2
  obtain ⟨ℓ, f, m, ℓo, fo, c, oa, ob, hu, hq, hg, hs⟩ := h n hn ε hε hε2
  refine ⟨ℓ, f, m, ℓo, fo, c, oa, ob, hu, hq, hg, ?_⟩
  intro w hw θ
  classical
  calc
    2 / 3 ≤ probEvent (act (c.unitary fun _ => memOracle n ℓ f w θ) (zeroKet m))
        (fun z => LearningCertificate ε w θ
          (WithLp.toLp 2 fun i => readFp (oa i) fo z) (readFp ob fo z)) := hs w hw θ
    _ ≤ probEvent (act (c.unitary fun _ => memOracle n ℓ f w θ) (zeroKet m))
        (fun z => disagree
          (ltf (WithLp.toLp 2 fun i => readFp (oa i) fo z) (readFp ob fo z))
          (ltf w θ) ≤ ε) := by
      unfold probEvent
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        simp only [Finset.mem_filter] at hz ⊢
        refine ⟨hz.1, ?_⟩
        exact learningCertificate_disagree hn ε hε hε2 w hw θ _ _ hz.2
      · intro z hz hnz
        unfold prob
        positivity
