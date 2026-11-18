-- Prove2me | solution 1 for QuantumLTF.Majority.intersection_transform_adversary_identity
-- status  : ACCEPTED   (disprove)
-- author  : @stockfish-soup
-- created : 2026-11-17T14:51:40.58822+00:00
-- url     : https://prove2.me/submissions/5d436930-36de-4a37-97d7-d0998621d4cd

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ¬ (∀ n r : ℕ, 1 ≤ r → r ≤ n →
    ∀ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 →
    (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) →
    let W := intersectionTransform r p q
    let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ :=
      fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)
    ∀ A B, A ≠ B →
      ∑ S : Qubits n,
        (if majorityBit A.1 S ≠ majorityBit B.1 S then X S A B else 0) = 1) := by
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
  have hbad := hfeas A B hAB
  let e : Bool × (Bool × Bool) ≃ Qubits 3 :=
    ((Equiv.refl Bool).prodCongr (piFinTwoEquiv (fun _ : Fin 2 ↦ Bool)).symm).trans
      (Fin.consEquiv (fun _ : Fin 3 ↦ Bool))
  rw [← Equiv.sum_comp e] at hbad
  simp [A, B, p, q, intersectionTransform, krawtchouk, intersectionIndex,
    majorityBit, Qubits, e, Fintype.sum_prod_type, Fintype.sum_bool,
    Fin.sum_univ_succ, Finset.sum_range_succ, Finset.filter_insert,
    Finset.filter_singleton] at hbad
  norm_num at hbad
