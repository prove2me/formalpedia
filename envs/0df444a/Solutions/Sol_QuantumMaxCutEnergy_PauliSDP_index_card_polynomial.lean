-- Prove2me | solution 1 for QuantumMaxCutEnergy.PauliSDP.index_card_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:46:14.756342+00:00
-- url     : https://prove2.me/submissions/64a0ec1c-a4bc-4509-b4be-66b786512f0c

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib

/-!
Polynomial cardinality of the actual support-truncated Pauli index set.
One induction step adds no label or one of three nonidentity labels at
one vertex. The covering map need not be injective; its surjectivity
gives the cardinality recurrence and the bound (3n+1)^k.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP.Cardinality

def nonzeroLabel (a : Fin 3) : Label := ⟨a.val + 1, by omega⟩

lemma support_update_zero {n : ℕ} (P : Word n) (i : Fin n) :
    support (Function.update P i 0) = (support P).erase i := by
  ext j
  by_cases h : j = i
  · subst j
    simp [support]
  · simp [support, Function.update_of_ne h, h]

lemma support_update_subset {n : ℕ} (P : Word n) (i : Fin n) (a : Label) :
    support (Function.update P i a) ⊆ insert i (support P) := by
  intro j hj
  by_cases h : j = i
  · simp [h]
  · apply Finset.mem_insert_of_mem
    have hn := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j, ?_⟩
    simpa only [Function.update_of_ne h] using hn

lemma support_update_card_le {n : ℕ} (P : Word n) (i : Fin n) (a : Label) :
    (support (Function.update P i a)).card ≤ (support P).card + 1 :=
  (Finset.card_le_card (support_update_subset P i a)).trans (Finset.card_insert_le _ _)

def extend {n k : ℕ} (r : Option (Fin n × Fin 3) × Index n k) : Index n (k + 1) :=
  match r.1 with
  | none => ⟨r.2.val, r.2.property.trans (Nat.le_succ k)⟩
  | some (i, a) => ⟨Function.update r.2.val i (nonzeroLabel a),
      (support_update_card_le r.2.val i (nonzeroLabel a)).trans
        (Nat.add_le_add_right r.2.property 1)⟩

theorem extend_surjective (n k : ℕ) : Function.Surjective (@extend n k) := by
  intro P
  classical
  by_cases hne : (support P.val).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hi0 : P.val i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hiNat : (P.val i).val ≠ 0 := by
      intro h
      exact hi0 (Fin.ext h)
    let a : Fin 3 := ⟨(P.val i).val - 1, by have hb := (P.val i).isLt; omega⟩
    have ha : nonzeroLabel a = P.val i := by
      apply Fin.ext
      dsimp [nonzeroLabel, a]
      omega
    have hpred : (support (Function.update P.val i 0)).card ≤ k := by
      rw [support_update_zero, Finset.card_erase_of_mem hi]
      have hp := P.property
      omega
    let Q : Index n k := ⟨Function.update P.val i 0, hpred⟩
    refine ⟨(some (i, a), Q), ?_⟩
    apply Subtype.ext
    funext j
    change Function.update (Function.update P.val i 0) i (nonzeroLabel a) j = P.val j
    by_cases hj : j = i
    · subst j
      simp [ha]
    · simp [Function.update_of_ne hj]
  · have hz : (support P.val).card = 0 := by
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    refine ⟨(none, ⟨P.val, by omega⟩), ?_⟩
    apply Subtype.ext
    rfl

theorem card_step (n k : ℕ) :
    Fintype.card (Index n (k + 1)) ≤ (3 * n + 1) * Fintype.card (Index n k) := by
  have h := Fintype.card_le_of_surjective (@extend n k) (extend_surjective n k)
  simpa [Nat.mul_comm] using h

lemma zero_support_word {n : ℕ} (P : Index n 0) : P.val = identityWord n := by
  funext i
  change P.val i = 0
  by_contra h
  have hi : i ∈ support P.val := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
  have hp : 0 < (support P.val).card := Finset.card_pos.mpr ⟨i, hi⟩
  have hz := P.property
  omega

theorem card_zero_le (n : ℕ) : Fintype.card (Index n 0) ≤ 1 := by
  have h := Fintype.card_le_of_injective (fun _ : Index n 0 => ()) (by
    intro P Q h
    apply Subtype.ext
    rw [zero_support_word P, zero_support_word Q])
  simpa using h

theorem index_card_bound (n k : ℕ) : Fintype.card (Index n k) ≤ (3 * n + 1) ^ k := by
  induction k with
  | zero => simpa using card_zero_le n
  | succ k ih =>
      calc
        _ ≤ (3 * n + 1) * Fintype.card (Index n k) := card_step n k
        _ ≤ (3 * n + 1) * (3 * n + 1) ^ k := Nat.mul_le_mul_left _ ih
        _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _

end QuantumMaxCutEnergy.PauliSDP.Cardinality

/-- For fixed k, the Gram matrix index has polynomial size in n.
The moment-coordinate index at degree2k obeys the corresponding bound. -/
theorem solution (n k : ℕ) :
    Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n k) ≤ (3 * n + 1) ^ k ∧
    Fintype.card (QuantumMaxCutEnergy.PauliSDP.Index n (2 * k)) ≤ (3 * n + 1) ^ (2 * k) :=
  ⟨QuantumMaxCutEnergy.PauliSDP.Cardinality.index_card_bound n k,
    QuantumMaxCutEnergy.PauliSDP.Cardinality.index_card_bound n (2 * k)⟩

#print axioms solution
