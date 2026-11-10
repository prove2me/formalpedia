-- Prove2me | solution 1 for QuantumMaxCutEnergy.sum_prod_bool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T14:21:40.007428+00:00
-- url     : https://prove2.me/submissions/ee7d4ed9-556e-4a1a-ae09-78e9b859f647

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


end QuantumMaxCutEnergy

open QuantumMaxCutEnergy in
theorem solution {n : ℕ} {R : Type*} [CommSemiring R] (F : Fin n → Bool → R) :
    (∑ x : Fin n → Bool, ∏ i, F i (x i))
      = ∏ i, (F i false + F i true) :=
  QuantumMaxCutEnergy.sum_prod_bool_proof F
