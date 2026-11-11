-- Prove2me | solution 1 for PauliUnclonable531.Pauli.preparation
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T09:50:08.354575+00:00
-- url     : https://prove2.me/submissions/48b0399e-f60e-424b-b8df-ca60a51263d0

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Ensemble

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


/-- The single-qubit computational projector `|a⟩⟨a|`. -/
def proj (a : Fin 2) : Op (Fin 2) := fun i j => if i = a ∧ j = a then 1 else 0

lemma basisDensity_eq_tens {n : ℕ} (r : Bits n) : basisDensity r = tens (fun j => proj (r j)) := by
  ext x y
  simp only [basisDensity, tens, proj]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, funext_iff]
  apply propext
  constructor
  · rintro ⟨h1, h2⟩ j; exact ⟨h1 j, h2 j⟩
  · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2⟩

lemma basisUnitary_eq_tens {n : ℕ} (k : Key n) :
    basisUnitary k = tens (fun j => basisChange (k.val.1 j) (k.val.2 j)) := rfl

lemma sum_tens {n : ℕ} (g : Fin n → Fin 2 → Op (Fin 2)) :
    (∑ r : Bits n, tens (fun j => g j (r j))) = tens (fun j => ∑ a, g j a) := by
  ext x y
  simp only [tens, Matrix.sum_apply]
  rw [Fintype.prod_sum]

lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1/2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma hconj2 : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

lemma qubit_complete (x z : Fin 2) :
    (∑ a, basisChange x z * proj a * (basisChange x z).conjTranspose) = 1 := by
  fin_cases x <;> fin_cases z <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [basisChange, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;>
    simp [gateMatrix, proj, hconj2, Matrix.one_fin_two] <;>
    (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq | (ring_nf; simp only [Complex.I_sq, sqrt2_inv_sq]; ring_nf))

lemma qubit_signed (x z : Fin 2) :
    (∑ a, sign (if decide (x ≠ 0 ∨ z ≠ 0) = true then a else 0) •
      (basisChange x z * proj a * (basisChange x z).conjTranspose)) =
      QMaxCutSDP.Rounding.pauli (localLabel x z) := by
  fin_cases x <;> fin_cases z <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [basisChange, Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;>
    simp [gateMatrix, proj, hconj2, sign, localLabel, QMaxCutSDP.Rounding.pauli, Matrix.one_fin_two] <;>
    (first | rfl | linear_combination (2:ℂ) * sqrt2_inv_sq | linear_combination (-2:ℂ) * sqrt2_inv_sq | linear_combination sqrt2_inv_sq | linear_combination (-1:ℂ) * sqrt2_inv_sq | linear_combination (2 * Complex.I) * sqrt2_inv_sq | linear_combination (-2 * Complex.I) * sqrt2_inv_sq | (ring_nf; simp only [Complex.I_sq, sqrt2_inv_sq]; ring_nf))

end PauliUnclonable531.Pauli.Kit

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Kit in
theorem solution (n : ℕ) (hn : 1 ≤ n) (k : Key n) (m : Fin 2) :
    ciphertext k m = parityEnsemble k m := by
  set ψ : Fin n → Fin 2 → Op (Fin 2) := fun j a =>
    basisChange (k.val.1 j) (k.val.2 j) * proj a * (basisChange (k.val.1 j) (k.val.2 j)).conjTranspose
    with hψ
  have hterm : ∀ r : Bits n, basisUnitary k * basisDensity r * (basisUnitary k).conjTranspose =
      tens (fun j => ψ j (r j)) := by
    intro r
    rw [basisUnitary_eq_tens, basisDensity_eq_tens, tens_conjTranspose, tens_mul, tens_mul]
  have hind : ∀ r : Bits n, (if weightedParity k r = m then
      basisUnitary k * basisDensity r * (basisUnitary k).conjTranspose else 0) =
      (1/2 : ℂ) • (tens (fun j => ψ j (r j)) + sign m •
        tens (fun j => sign (if active k.val j then r j else 0) • ψ j (r j))) := by
    intro r
    rw [hterm, tens_smul, ← sign_sum, smul_smul]
    have : sign m * sign (∑ j, if active k.val j = true then r j else 0) =
        if weightedParity k r = m then 1 else -1 := by
      unfold weightedParity
      generalize (∑ j, if active k.val j = true then r j else 0) = w
      fin_cases m <;> fin_cases w <;> simp [sign]
    rw [this]
    split_ifs
    · rw [one_smul, ← two_smul ℂ, smul_smul]; norm_num
    · rw [neg_one_smul, add_neg_cancel, smul_zero]
  rw [parityEnsemble]
  simp only [hind]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [sum_tens, sum_tens (fun j a => sign (if active k.val j then a else 0) • ψ j a)]
  have h1 : (fun j => ∑ a, ψ j a) = fun _ => (1 : Op (Fin 2)) := by
    funext j; exact qubit_complete _ _
  have h2 : (fun j => ∑ a, sign (if active k.val j then a else 0) • ψ j a) =
      fun j => QMaxCutSDP.Rounding.pauli (localLabel (k.val.1 j) (k.val.2 j)) := by
    funext j; exact qubit_signed _ _
  rw [h1, h2, tens_one, ← pauli_eq_tens, ciphertext, smul_smul]
  congr 1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  field_simp
