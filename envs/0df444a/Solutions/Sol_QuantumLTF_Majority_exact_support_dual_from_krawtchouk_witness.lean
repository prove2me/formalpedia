-- Prove2me | solution 1 for QuantumLTF.Majority.exact_support_dual_from_krawtchouk_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:40:20.376142+00:00
-- url     : https://prove2.me/submissions/ba4f9adb-c6b6-490b-8d28-05dd353fb614
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_lemma_4_1
import Theorems.Thm_QuantumLTF_Majority_exact_support_krawtchouk_cost

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, 3 ≤ r → r ≤ n →
    ∀ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 →
    (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r →
      (p t = 0 ↔ q t ≠ 0)) →
    (∑ t : Fin (r+1), (r.choose t : ℝ) *
      ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 →
    ∀ T : ℝ, (∑ t : Fin (r+1), (r.choose t : ℝ) *
      (p t^2 + q t^2)) ≤ T →
    ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ,
      DualFeasible (fun A : ExactSupports n r => A.1) X ∧
      DualCostAtMost X T := by
  intro n r hr hrn p q hnorm hsupp hcross T henergy
  let W := intersectionTransform r p q
  let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ :=
    fun S A B => (2 : ℝ) ^ (-n : ℤ) * W (intersectionIndex A S) *
      W (intersectionIndex B S)
  have hfeas : DualFeasible (fun A : ExactSupports n r => A.1) X := by
    exact lemma_4_1 n r (by omega) hrn p q hnorm hsupp
  have hcost : DualCostAtMost X T := by
    exact exact_support_krawtchouk_cost n r hrn p q hcross T henergy
  exact ⟨X, hfeas, hcost⟩

