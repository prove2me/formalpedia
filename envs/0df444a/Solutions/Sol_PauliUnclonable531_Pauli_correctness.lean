-- Prove2me | solution 1 for PauliUnclonable531.Pauli.correctness
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:18:51.667283+00:00
-- url     : https://prove2.me/submissions/f553f811-dba4-415f-a4da-123716818b21

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Scheme
import Theorems.Thm_PauliUnclonable531_Pauli_pauli_bridges

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


lemma qubitPauli_trace (a : Fin 4) (ha : a ≠ 0) : (QMaxCutSDP.Rounding.pauli a).trace = 0 := by
  fin_cases a
  · exact absurd rfl ha
  all_goals simp [QMaxCutSDP.Rounding.pauli, Matrix.trace, Fin.sum_univ_two]

lemma pauli_trace {n : ℕ} (k : Label n) (hk : k ≠ (0, 0)) : (pauli k).trace = 0 := by
  have hex : ∃ j, localLabel (k.1 j) (k.2 j) ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    apply hk
    have h1 : ∀ j, k.1 j = 0 ∧ k.2 j = 0 := by
      intro j
      have := hne j
      revert this
      unfold localLabel
      generalize k.1 j = x
      generalize k.2 j = z
      fin_cases x <;> fin_cases z <;> simp
    exact Prod.ext (funext fun j => (h1 j).1) (funext fun j => (h1 j).2)
  obtain ⟨j, hj⟩ := hex
  rw [pauli_eq_tens, tens_trace]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (qubitPauli_trace _ hj)

end PauliUnclonable531.Pauli.Kit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Kit in
theorem solution (n : ℕ) (hn : 1 ≤ n) (k : Key n) (m m' : Fin 2) :
    born (decryptEffect k m') (ciphertext k m) = if m' = m then 1 else 0 := by
  have hP := (pauli_bridges n k.val).1
  have htr := pauli_trace k.val k.property
  have hexp : (1 + sign m' • pauli k.val) * (1 + sign m • pauli k.val) =
      (1 + sign m' * sign m) • (1 : Op (Bits n)) + (sign m' + sign m) • pauli k.val := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP]
    module
  unfold born decryptEffect ciphertext
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hexp, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, htr, Matrix.trace_one]
  have hcard : (Fintype.card (Bits n) : ℂ) = ((2 ^ n : ℝ) : ℂ) := by simp [Bits]
  have h2 : ((2 : ℂ) ^ n) = ((2 ^ n : ℝ) : ℂ) := by push_cast; rfl
  have hpos : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [hcard, h2]
  generalize (2 : ℝ) ^ n = x at hpos ⊢
  have hx : (x : ℂ) ≠ 0 := by exact_mod_cast hpos
  fin_cases m <;> fin_cases m' <;> simp only [sign, smul_eq_mul, mul_zero, add_zero] <;> norm_num
  all_goals field_simp
