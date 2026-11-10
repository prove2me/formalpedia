-- Prove2me | solution 1 for QuantumMaxCutEnergy.squaredNorm_prodState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:21:44.001246+00:00
-- url     : https://prove2.me/submissions/40b5fecd-30bd-45ee-819f-296513ba2b5d

import Mathlib
import Definitions.Def_QuantumMaxCutEnergy_prodState

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy
/-- `normSq` of a finite product is the product of the `normSq`s. -/
theorem normSq_prod_proof {n : ℕ} (f : Fin n → ℂ) :
    Complex.normSq (∏ i, f i) = ∏ i, Complex.normSq (f i) := by
  have key : ∀ s : Finset (Fin n),
      Complex.normSq (∏ i ∈ s, f i) = ∏ i ∈ s, Complex.normSq (f i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.normSq_mul, ih]
  simpa using key Finset.univ

/-- **Sum of a product over a product of index sets.** -/
theorem sum_prod_bool_proof {n : ℕ} {R : Type*} [CommSemiring R] (F : Fin n → Bool → R) :
    (∑ x : Fin n → Bool, ∏ i, F i (x i))
      = ∏ i, (F i false + F i true) := by
  have hpi : (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)))
      = Finset.univ := by
    ext x
    simp
  rw [← hpi, ← Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset Bool))
    (f := F)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, add_comm]

/-- **The squared norm of a product state is the product of the per-qubit norms.** -/
theorem squaredNorm_prodState_proof {n : ℕ} (α β : Fin n → ℂ) :
    squaredNorm (prodState α β)
      = ∏ i, (Complex.normSq (α i) + Complex.normSq (β i)) := by
  unfold squaredNorm prodState
  have h : ∀ x : Fin n → Bool,
      Complex.normSq (∏ i, if x i then β i else α i)
        = ∏ i, (if x i then Complex.normSq (β i) else Complex.normSq (α i)) := by
    intro x
    rw [normSq_prod_proof]
    exact Finset.prod_congr rfl fun i _ => by cases hx : x i <;> simp [hx]
  simp only [h]
  rw [sum_prod_bool_proof (F := fun i (b : Bool) =>
    if b then Complex.normSq (β i) else Complex.normSq (α i))]
  exact Finset.prod_congr rfl fun i _ => by simp

/-- **Unit amplitudes give a normalised state.** -/
theorem squaredNorm_prodState_proof_eq_one {n : ℕ} (α β : Fin n → ℂ)
    (h : ∀ i, Complex.normSq (α i) + Complex.normSq (β i) = 1) :
    squaredNorm (prodState α β) = 1 := by
  rw [squaredNorm_prodState_proof]
  rw [Finset.prod_eq_one]
  intro i _
  exact h i

end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution {n : ℕ} (α β : Fin n → ℂ) :
    squaredNorm (prodState α β)
      = ∏ i, (Complex.normSq (α i) + Complex.normSq (β i)) :=
  QuantumMaxCutEnergy.squaredNorm_prodState_proof α β
