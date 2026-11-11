-- Prove2me | solution 1 for PauliUnclonable531.Pauli.pauli_bridges
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:11:02.689938+00:00
-- url     : https://prove2.me/submissions/e7b21b36-e66f-49ea-94c6-2939a053bf29

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Keys

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Kit


open PauliUnclonable531.Pauli

/-- The tensor product `⊗ᵢ fᵢ` of single-qubit matrices, on the computational basis. -/
def tens {n : ℕ} (f : Fin n → Op (Fin 2)) : Op (Bits n) := fun x y => ∏ i, f i (x i) (y i)

lemma tens_mul {n : ℕ} (f g : Fin n → Op (Fin 2)) :
    tens f * tens g = tens (fun i => f i * g i) := by
  ext x y
  simp only [tens, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

lemma tens_one {n : ℕ} : tens (fun _ : Fin n => (1 : Op (Fin 2))) = 1 := by
  ext x y
  simp only [tens, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma tens_smul {n : ℕ} (c : Fin n → ℂ) (f : Fin n → Op (Fin 2)) :
    tens (fun i => c i • f i) = (∏ i, c i) • tens f := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).conjTranspose = tens (fun i => (f i).conjTranspose) := by
  ext x y
  simp [tens, star_prod]

lemma tens_transpose {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).transpose = tens (fun i => (f i).transpose) := by
  ext x y
  simp [tens]

lemma tens_trace {n : ℕ} (f : Fin n → Op (Fin 2)) :
    (tens f).trace = ∏ i, (f i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Fintype.prod_sum]

lemma pauli_eq_tens {n : ℕ} (k : Label n) :
    pauli k = tens (fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.1 j) (k.2 j))) := rfl

lemma sign_add (a b : Fin 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sum {ι : Type} (s : Finset ι) (f : ι → Fin 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]


lemma qubit_sq (a : Fin 4) : QMaxCutSDP.Rounding.pauli a * QMaxCutSDP.Rounding.pauli a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QMaxCutSDP.Rounding.pauli, Matrix.mul_apply, Fin.sum_univ_two]

lemma qubit_transpose (x z : Fin 2) :
    (QMaxCutSDP.Rounding.pauli (localLabel x z)).transpose =
      sign (x * z) • QMaxCutSDP.Rounding.pauli (localLabel x z) := by
  fin_cases x <;> fin_cases z <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [QMaxCutSDP.Rounding.pauli, localLabel, sign]

end PauliUnclonable531.Pauli.Kit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Kit in
theorem solution (n : ℕ) (k : Label n) :
    pauli k * pauli k = 1 ∧
    (pauli k).transpose * (pauli k).transpose = 1 ∧
    (pauli k).transpose = sign (∑ j, k.1 j * k.2 j) • pauli k := by
  have h1 : pauli k * pauli k = 1 := by
    rw [pauli_eq_tens, tens_mul]
    simp only [qubit_sq]
    exact tens_one
  refine ⟨h1, ?_, ?_⟩
  · rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  · rw [pauli_eq_tens, tens_transpose]
    simp only [qubit_transpose]
    rw [tens_smul, sign_sum]
