-- Prove2me | solution 1 for PauliUnclonable531.Pauli.pauli_commutation
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:15:04.989467+00:00
-- url     : https://prove2.me/submissions/6670f009-c191-4806-beb5-c3b8c173bda8

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Symplectic

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


lemma qubit_comm (x z x' z' : Fin 2) :
    QMaxCutSDP.Rounding.pauli (localLabel x z) * QMaxCutSDP.Rounding.pauli (localLabel x' z') =
      sign (x * z' + z * x') •
        (QMaxCutSDP.Rounding.pauli (localLabel x' z') * QMaxCutSDP.Rounding.pauli (localLabel x z)) := by
  fin_cases x <;> fin_cases z <;> fin_cases x' <;> fin_cases z' <;> ext i j <;> fin_cases i <;>
    fin_cases j <;> simp [QMaxCutSDP.Rounding.pauli, localLabel, sign, Matrix.mul_apply, Fin.sum_univ_two]

end PauliUnclonable531.Pauli.Kit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Kit in
theorem solution (n : ℕ) (k l : Label n) :
    pauli k * pauli l = sign (symplectic k l) • (pauli l * pauli k) ∧
    (pauli k).transpose * (pauli l).transpose =
      sign (symplectic k l) • ((pauli l).transpose * (pauli k).transpose) := by
  have h : ∀ k l : Label n, pauli k * pauli l = sign (symplectic k l) • (pauli l * pauli k) := by
    intro k l
    rw [pauli_eq_tens, pauli_eq_tens, tens_mul, tens_mul]
    have hfun : (fun i => QMaxCutSDP.Rounding.pauli (localLabel (k.1 i) (k.2 i)) *
        QMaxCutSDP.Rounding.pauli (localLabel (l.1 i) (l.2 i))) = fun i =>
        sign (k.1 i * l.2 i + k.2 i * l.1 i) •
          (QMaxCutSDP.Rounding.pauli (localLabel (l.1 i) (l.2 i)) *
            QMaxCutSDP.Rounding.pauli (localLabel (k.1 i) (k.2 i))) :=
      funext fun i => qubit_comm _ _ _ _
    rw [hfun, tens_smul, symplectic, sign_sum]
  have hsymm : symplectic l k = symplectic k l := by
    unfold symplectic
    apply Finset.sum_congr rfl
    intro j _
    rw [add_comm, mul_comm (l.2 j), mul_comm (l.1 j)]
  refine ⟨h k l, ?_⟩
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h l k, hsymm, Matrix.transpose_smul]
