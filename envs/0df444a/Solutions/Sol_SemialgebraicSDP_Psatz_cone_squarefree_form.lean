-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.cone_squarefree_form
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:22:26.991235+00:00
-- url     : https://prove2.me/submissions/f75f5f83-4755-4cd3-8421-e08c79b23765

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Cone

namespace SemialgebraicSDP.Psatz
open MvPolynomial

private def Rep {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (x : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ p : Finset (Fin s) → MvPolynomial (Fin n) ℝ,
    (∀ T, IsSumSq (p T)) ∧ x = ∑ T, p T * ∏ j ∈ T, f j

private theorem rep_term {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (T : Finset (Fin s)) (a : MvPolynomial (Fin n) ℝ) (ha : IsSumSq a) :
    Rep f (a * ∏ j ∈ T, f j) := by
  classical
  refine ⟨fun U => if U = T then a else 0, ?_, ?_⟩
  · intro U
    dsimp
    split_ifs
    · exact ha
    · exact IsSumSq.zero
  · simp

private theorem rep_add {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    {a b : MvPolynomial (Fin n) ℝ} (ha : Rep f a) (hb : Rep f b) : Rep f (a + b) := by
  classical
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hb
  refine ⟨fun T => p T + q T, fun T => (hp T).add (hq T), ?_⟩
  simp only [add_mul, Finset.sum_add_distrib]

private theorem rep_sum {n s : ℕ} {ι : Type*}
    (f : Fin s → MvPolynomial (Fin n) ℝ) (I : Finset ι)
    (a : ι → MvPolynomial (Fin n) ℝ) (ha : ∀ i ∈ I, Rep f (a i)) :
    Rep f (∑ i ∈ I, a i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, fun _ => IsSumSq.zero, by simp⟩
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact rep_add f (ha i (Finset.mem_insert_self _ _))
      (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

private theorem prod_squarefree {n s : ℕ}
    (f : Fin s → MvPolynomial (Fin n) ℝ) (T U : Finset (Fin s)) :
    (∏ j ∈ T, f j) * (∏ j ∈ U, f j) =
      (∏ j ∈ T ∩ U, f j) ^ 2 * ∏ j ∈ (T \ U) ∪ (U \ T), f j := by
  classical
  have he (V : Finset (Fin s)) :
      (∏ j ∈ V, f j) = ∏ j : Fin s, if j ∈ V then f j else 1 := by
    simp
  simp only [he, pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases ht : j ∈ T <;> by_cases hu : j ∈ U <;> simp [ht, hu]

private theorem rep_mul {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    {a b : MvPolynomial (Fin n) ℝ} (ha : Rep f a) (hb : Rep f b) : Rep f (a * b) := by
  classical
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := hb
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply rep_sum
  intro U _
  apply rep_sum
  intro T _
  have he : (p T * ∏ j ∈ T, f j) * (q U * ∏ j ∈ U, f j) =
      (p T * q U * (∏ j ∈ T ∩ U, f j) ^ 2) *
        ∏ j ∈ (T \ U) ∪ (U \ T), f j := by
    calc
      _ = p T * q U * ((∏ j ∈ T, f j) * ∏ j ∈ U, f j) := by ring
      _ = _ := by rw [prod_squarefree]; ring
  rw [he]
  apply rep_term
  exact ((hp T).mul (hq U)).mul (by simpa [pow_two] using IsSumSq.mul_self (∏ j ∈ T ∩ U, f j))

private theorem sos_inCone {n : ℕ} (S : Set (MvPolynomial (Fin n) ℝ))
    {a : MvPolynomial (Fin n) ℝ} (ha : IsSumSq a) : InCone S a := by
  induction ha with
  | zero => simpa using InCone.sq (S := S) 0
  | sq_add a h ih =>
    exact InCone.add (by simpa [pow_two] using InCone.sq (S := S) a) ih

private theorem cone_sum {n : ℕ} {ι : Type*} (S : Set (MvPolynomial (Fin n) ℝ))
    (I : Finset ι) (a : ι → MvPolynomial (Fin n) ℝ) (ha : ∀ i ∈ I, InCone S (a i)) :
    InCone S (∑ i ∈ I, a i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using InCone.sq (S := S) 0
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact InCone.add (ha i (Finset.mem_insert_self _ _))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

private theorem cone_prod {n : ℕ} {ι : Type*} (S : Set (MvPolynomial (Fin n) ℝ))
    (I : Finset ι) (a : ι → MvPolynomial (Fin n) ℝ) (ha : ∀ i ∈ I, InCone S (a i)) :
    InCone S (∏ i ∈ I, a i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using InCone.sq (S := S) 1
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi]
    exact InCone.mul (ha i (Finset.mem_insert_self _ _))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

theorem cone_squarefree_form {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (x : MvPolynomial (Fin n) ℝ) :
    x ∈ cone (Set.range f) ↔
      ∃ p : Finset (Fin s) → MvPolynomial (Fin n) ℝ,
        (∀ T, IsSumSq (p T)) ∧ x = ∑ T : Finset (Fin s), p T * ∏ j ∈ T, f j := by
  classical
  constructor
  · intro hx
    change InCone (Set.range f) x at hx
    change Rep f x
    induction hx with
    | of_mem h =>
      obtain ⟨j, rfl⟩ := h
      simpa using rep_term f {j} 1 IsSumSq.one
    | sq a =>
      simpa using rep_term f ∅ (a ^ 2) (by simpa [pow_two] using IsSumSq.mul_self a)
    | add ha hb iha ihb => exact rep_add f iha ihb
    | mul ha hb iha ihb => exact rep_mul f iha ihb
  · rintro ⟨p, hp, rfl⟩
    apply cone_sum
    intro T _
    apply InCone.mul (sos_inCone _ (hp T))
    apply cone_prod
    intro j _
    exact InCone.of_mem (Set.mem_range_self j)

end SemialgebraicSDP.Psatz

open SemialgebraicSDP.Psatz MvPolynomial

theorem solution {n s : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (x : MvPolynomial (Fin n) ℝ) :
    x ∈ cone (Set.range f) ↔
      ∃ p : Finset (Fin s) → MvPolynomial (Fin n) ℝ,
        (∀ T, IsSumSq (p T)) ∧ x = ∑ T : Finset (Fin s), p T * ∏ j ∈ T, f j :=
  SemialgebraicSDP.Psatz.cone_squarefree_form f x

#print axioms solution
