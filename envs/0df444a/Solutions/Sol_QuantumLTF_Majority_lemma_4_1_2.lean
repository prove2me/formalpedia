-- Prove2me | solution 2 for QuantumLTF.Majority.lemma_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @stockfish-soup
-- created : 2026-11-17T14:54:22.782448+00:00
-- url     : https://prove2.me/submissions/dde9d7c7-57d2-4592-bb3a-369b693f7275

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ¬ (∀ n k : ℕ, 1 ≤ k → k ≤ n →
    ∀ p q : Fin (k+1) → ℝ, p 0 * q 0 = 1/2 →
    (∀ t : Fin (k+1), 1 ≤ t.1 → t.1 < k → (p t = 0 ↔ q t ≠ 0)) →
    let W := intersectionTransform k p q
    let X : Qubits n → Matrix (ExactSupports n k) (ExactSupports n k) ℝ :=
      fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)
    DualFeasible (fun A : ExactSupports n k => A.1) X) := by
  intro h
  let p : Fin 3 → ℝ := ![1, 0, 0]
  let q : Fin 3 → ℝ := ![1/2, 1, 0]
  have hpq : p 0 * q 0 = (1 / 2 : ℝ) := by norm_num [p, q]
  have hsupp : ∀ t : Fin 3, 1 ≤ (t : ℕ) → (t : ℕ) < 2 →
      (p t = 0 ↔ q t ≠ 0) := by
    intro t ht ht2
    have htval : (t : ℕ) = 1 := by omega
    have : t = (1 : Fin 3) := Fin.ext htval
    subst t
    norm_num [p, q]
  have hfeas := h 3 2 (by omega) (by omega) p q hpq hsupp
  let A : ExactSupports 3 2 := ⟨{0, 1}, by decide⟩
  let B : ExactSupports 3 2 := ⟨{0, 2}, by decide⟩
  have hAB : A ≠ B := by decide
  have hbad := hfeas.2 A B hAB
  let e : Bool × (Bool × Bool) ≃ Qubits 3 :=
    ((Equiv.refl Bool).prodCongr (piFinTwoEquiv (fun _ : Fin 2 ↦ Bool)).symm).trans
      (Fin.consEquiv (fun _ : Fin 3 ↦ Bool))
  rw [← Equiv.sum_comp e] at hbad
  simp [A, B, p, q, intersectionTransform, krawtchouk, intersectionIndex,
    majorityBit, Qubits, e, Fintype.sum_prod_type, Fintype.sum_bool,
    Fin.sum_univ_succ, Finset.sum_range_succ, Finset.filter_insert,
    Finset.filter_singleton] at hbad
  norm_num at hbad
