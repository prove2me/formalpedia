-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.theorem9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:22:46.531341+00:00
-- url     : https://prove2.me/submissions/6d5166fa-aeb6-43d8-8e10-91ba2860f3da

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.


theorem s110t9_swap_trace {I : Type*} [Fintype I] [DecidableEq I] (A : Mat I) :
    (tensorPower 2 A * copySwap I).trace = (A * A).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, copySwap, tensorPower]
  have hc : ∀ x y : Fin 2 → I, (y 0 = x 1 ∧ y 1 = x 0) ↔ y = ![x 1, x 0] := by
    intro x y
    constructor
    · rintro ⟨h0, h1⟩; ext i; fin_cases i <;> simp [h0, h1]
    · rintro rfl; simp
  simp only [hc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← (finTwoArrowEquiv I).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.prod_univ_two, finTwoArrowEquiv]

theorem s110t9_swap_herm {I : Type*} [DecidableEq I] :
    (copySwap I).conjTranspose = copySwap I := by
  ext x y
  simp only [Matrix.conjTranspose_apply, copySwap]
  by_cases h : (y 0 = x 1 ∧ y 1 = x 0)
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp

theorem s110t9_swap_sq {I : Type*} [Fintype I] [DecidableEq I] :
    copySwap I * copySwap I = 1 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single ![x 1, x 0]]
  · simp only [copySwap, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [funext_iff, Fin.forall_fin_two, and_comm]
  · intro z _ hz
    simp only [copySwap]
    rw [if_neg, zero_mul]
    rintro ⟨h0, h1⟩
    exact hz (by ext i; fin_cases i <;> simp [h0, h1])
  · simp

def s110t9_P0 : Mat Bool := Matrix.diagonal fun a => if a then 0 else 1
def s110t9_P1 : Mat Bool := Matrix.diagonal fun a => if a then 1 else 0

theorem s110t9_ctrl {I : Type*} [Fintype I] [DecidableEq I] (S : Mat I) :
    controlled S = Matrix.kronecker s110t9_P0 1 + Matrix.kronecker s110t9_P1 S := by
  ext ⟨a, x⟩ ⟨b, y⟩
  cases a <;> cases b <;>
    simp [controlled, Matrix.kronecker_apply, s110t9_P0, s110t9_P1, Matrix.diagonal]

def s110t9_A : Mat Bool := Matrix.of fun _ _ => 1 / 2
def s110t9_B : Mat Bool := Matrix.of fun a b => if a = b then 1 / 2 else -1 / 2

theorem s110t9_s : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

theorem s110t9_HA : hadamard * s110t9_P0 * hadamard = s110t9_A := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, hadamard, s110t9_P0, s110t9_A, Matrix.diagonal,
      s110t9_s]

theorem s110t9_HB : hadamard * s110t9_P1 * hadamard = s110t9_B := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, hadamard, s110t9_P1, s110t9_B, Matrix.diagonal,
      s110t9_s] <;> norm_num

theorem s110t9_U {I : Type*} [Fintype I] [DecidableEq I] :
    swapTestMatrix I = Matrix.kronecker s110t9_A 1 + Matrix.kronecker s110t9_B (copySwap I) := by
  unfold swapTestMatrix
  rw [s110t9_ctrl, Matrix.mul_add, Matrix.add_mul]
  unfold Matrix.kronecker
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, s110t9_HA, s110t9_HB]

theorem s110t9_sandwich {I : Type*} [Fintype I] [DecidableEq I] (A B M : Mat Bool) :
    (Matrix.kronecker A 1 + Matrix.kronecker B (copySwap I)).conjTranspose *
      Matrix.kronecker M (1 : Mat (Copies I 2)) *
      (Matrix.kronecker A 1 + Matrix.kronecker B (copySwap I)) =
    Matrix.kronecker (A.conjTranspose * M * A + B.conjTranspose * M * B) 1 +
      Matrix.kronecker (A.conjTranspose * M * B + B.conjTranspose * M * A) (copySwap I) := by
  unfold Matrix.kronecker
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    s110t9_swap_herm, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, s110t9_swap_sq, Matrix.add_kronecker]
  abel

theorem s110t9_c1 : s110t9_A.conjTranspose * s110t9_A + s110t9_B.conjTranspose * s110t9_B = 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, s110t9_A, s110t9_B, map_ofNat] <;> norm_num

theorem s110t9_c2 : s110t9_A.conjTranspose * s110t9_B + s110t9_B.conjTranspose * s110t9_A = 0 := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, s110t9_A, s110t9_B, map_ofNat] <;> norm_num

theorem s110t9_c3 : s110t9_A.conjTranspose * pauliZ * s110t9_A +
    s110t9_B.conjTranspose * pauliZ * s110t9_B = 0 := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, s110t9_A, s110t9_B, pauliZ, Matrix.diagonal, map_ofNat] <;>
    norm_num

theorem s110t9_c4 : s110t9_A.conjTranspose * pauliZ * s110t9_B +
    s110t9_B.conjTranspose * pauliZ * s110t9_A = pauliZ := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, s110t9_A, s110t9_B, pauliZ, Matrix.diagonal, map_ofNat] <;>
    norm_num

theorem s110t9_unitary (I : Type*) [Fintype I] [DecidableEq I] :
    swapTestMatrix I ∈ Matrix.unitaryGroup (Bool × Copies I 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, s110t9_U]
  have := s110t9_sandwich (I := I) s110t9_A s110t9_B 1
  unfold Matrix.kronecker at this ⊢
  simp only [Matrix.mul_one, Matrix.one_kronecker_one] at this
  rw [this, s110t9_c1, s110t9_c2, Matrix.one_kronecker_one, Matrix.zero_kronecker, add_zero]

theorem s110t9_eff (I : Type*) [Fintype I] [DecidableEq I] :
    (swapTestMatrix I).conjTranspose * Matrix.kronecker pauliZ (1 : Mat (Copies I 2)) *
      swapTestMatrix I = Matrix.kronecker pauliZ (copySwap I) := by
  rw [s110t9_U, s110t9_sandwich, s110t9_c3, s110t9_c4]
  unfold Matrix.kronecker
  rw [Matrix.zero_kronecker, zero_add]

theorem s110t9_zherm : pauliZ.IsHermitian := by
  ext a b
  cases a <;> cases b <;> simp [pauliZ, Matrix.diagonal]

def s110t9_model (n : ℕ) : AncillaModel (Qubits n) where
  unitary := ⟨swapTestMatrix (Qubits n), s110t9_unitary _⟩
  observable := pauliZ
  hermitian := s110t9_zherm

theorem s110t9_resp (n : ℕ) (rho : Mat (Qubits n)) :
    (s110t9_model n).response rho = purity rho := by
  unfold AncillaModel.response purity
  congr 1
  change (swapTestMatrix (Qubits n) * _ * (swapTestMatrix (Qubits n)).conjTranspose *
    Matrix.kronecker pauliZ (1 : Mat (Copies (Qubits n) 2))).trace = _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [s110t9_eff]
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, s110t9_swap_trace]
  have : (pureDensity (ket false) * pauliZ : Mat Bool).trace = 1 := by
    simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_bool, pureDensity, ket, pauliZ,
      Matrix.diagonal]
  rw [this, one_mul]

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P32 (purity)

theorem solution {n : ℕ} (hn : 1 ≤ n) (b : ℝ)
    (hb : 1 / (2 : ℝ) ^ n ≤ b ∧ b < 1)
    (hpure : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = 1)
    (hmixed : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = b) :
    ∃ M : AncillaModel (Qubits n),
      (M.unitary : Mat (Bool × Copies (Qubits n) 2)) = swapTestMatrix (Qubits n) ∧
      M.observable = pauliZ ∧
      M.effective = Matrix.kronecker pauliZ (copySwap (Qubits n)) ∧
      act pauliZ (ket false) = ket false ∧
      DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
        {rho | IsDensityMatrix rho} M.response ∧
      (∀ rho, IsDensityMatrix rho → M.response rho = purity rho) ∧
      SeparatesPurity b M.response := by
  refine ⟨s110t9_model n, rfl, rfl, s110t9_eff _, ?_, ?_, fun rho _ => s110t9_resp n rho, ?_⟩
  · ext a
    cases a <;> simp [act, ket, pauliZ, Matrix.mulVec, dotProduct, Matrix.diagonal,
      Fintype.sum_bool]
  · intro V hV rho _
    rw [s110t9_resp, s110t9_resp]
    have hV' : V.conjTranspose * V = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hV
      simpa [Matrix.star_eq_conjTranspose] using this
    simp only [purity, conjSuperop]
    have : V * rho * V.conjTranspose * (V * rho * V.conjTranspose)
        = V * (rho * rho * V.conjTranspose) := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc V.conjTranspose V, hV', Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hV', Matrix.mul_one]
  · intro rho sigma _ _ h1 hbq heq
    rw [s110t9_resp, s110t9_resp, h1, hbq] at heq
    linarith [hb.2]

end
