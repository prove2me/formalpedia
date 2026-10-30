-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:00:42.470508+00:00
-- url     : https://prove2.me/submissions/70b51faf-bebf-473d-ab87-e7ce707cf57f

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

attribute [local instance 100] LieRing.ofAssociativeRing

theorem s110k_tp_mul {I : Type*} [Fintype I] (k : ℕ) (A B : Mat I) :
    tensorPower k (A * B) = tensorPower k A * tensorPower k B := by
  ext x y
  simp only [tensorPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

theorem s110k_tp_conjT {I : Type*} (k : ℕ) (V : Mat I) :
    tensorPower k V.conjTranspose = (tensorPower k V).conjTranspose := by
  ext a b
  simp [tensorPower, Matrix.conjTranspose_apply, star_prod]

theorem s110k_tp_one {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) :
    tensorPower k (1 : Mat I) = 1 := by
  ext x y
  simp only [tensorPower, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem s110k_tp_unitary {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (V : Mat I)
    (hV : V.conjTranspose * V = 1) :
    (tensorPower k V).conjTranspose * tensorPower k V = 1 := by
  rw [← s110k_tp_conjT, ← s110k_tp_mul, hV, s110k_tp_one]

theorem s110k_response_eq {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) (rho : Mat I) :
    M.response rho = (tensorPower k rho * M.effective).trace.re := by
  unfold ExpectationModel.response ExpectationModel.effective
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem s110k_response_conj {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) (V : Mat I) (hV : V.conjTranspose * V = 1)
    (hc : M.effective * tensorPower k V = tensorPower k V * M.effective) (rho : Mat I) :
    M.response (conjSuperop V rho) = M.response rho := by
  rw [s110k_response_eq, s110k_response_eq]
  congr 1
  have hW := s110k_tp_unitary k V hV
  simp only [conjSuperop, s110k_tp_mul, s110k_tp_conjT]
  set W := tensorPower k V
  set E := M.effective
  set T := tensorPower k rho
  calc (W * T * W.conjTranspose * E).trace
      = (W * (T * W.conjTranspose * E)).trace := by simp only [Matrix.mul_assoc]
    _ = (T * W.conjTranspose * E * W).trace := Matrix.trace_mul_comm _ _
    _ = (T * (W.conjTranspose * W) * E).trace := by
        simp only [Matrix.mul_assoc, hc]
    _ = (T * E).trace := by rw [hW, Matrix.mul_one]

theorem s110k_invariant {n k : ℕ} (M : ExpectationModel (Qubits n) k)
    (G : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ)) (R : Set (Mat (Qubits n)))
    (hcomm : M.effective ∈ tensorCommutant k (groupMatrices G)) :
    DomainInvariant (groupMatrices G) R M.response := by
  intro V hV rho _
  have hV' := hV
  obtain ⟨u, hu, rfl⟩ := hV'
  apply s110k_response_conj
  · have := Matrix.mem_unitaryGroup_iff'.mp u.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · unfold tensorCommutant at hcomm
    exact hcomm _ ⟨_, hV, rfl⟩


theorem s110k_tp_trace {I : Type*} [Fintype I] (k : ℕ) (A : Mat I) :
    (tensorPower k A).trace = A.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem s110k_swap_trace {I : Type*} [Fintype I] [DecidableEq I] (A : Mat I) :
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

theorem s110k_swap_herm {I : Type*} [DecidableEq I] :
    (copySwap I).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, copySwap]
  by_cases h : (y 0 = x 1 ∧ y 1 = x 0)
  · rw [if_pos h, if_pos ⟨h.2.symm, h.1.symm⟩]; simp
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)]; simp

open scoped ComplexOrder in
theorem s110k_density_conj {I : Type*} [Fintype I] [DecidableEq I] (V rho : Mat I)
    (hV : V.conjTranspose * V = 1) (hr : IsDensityMatrix rho) :
    IsDensityMatrix (conjSuperop V rho) ∧ purity (conjSuperop V rho) = purity rho := by
  refine ⟨⟨hr.1.mul_mul_conjTranspose_same V, ?_⟩, ?_⟩
  · simp only [conjSuperop]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]; exact hr.2
  · simp only [purity, conjSuperop]
    have : V * rho * V.conjTranspose * (V * rho * V.conjTranspose)
        = V * (rho * rho * V.conjTranspose) := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc V.conjTranspose V, hV, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hV, Matrix.mul_one]

def s110k_model (n : ℕ) (a s : ℝ) : ExpectationModel (Qubits n) 2 where
  unitary := 1
  observable := (a : ℂ) • 1 + (s : ℂ) • copySwap (Qubits n)
  hermitian := by
    apply Matrix.IsHermitian.add
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]; simp
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, s110k_swap_herm.eq]; simp

theorem s110k_model_eff (n : ℕ) (a s : ℝ) :
    (s110k_model n a s).effective = (a : ℂ) • 1 + (s : ℂ) • copySwap (Qubits n) := by
  simp [ExpectationModel.effective, s110k_model]

theorem s110k_model_resp (n : ℕ) (a s : ℝ) (rho : Mat (Qubits n)) (hr : IsDensityMatrix rho) :
    (s110k_model n a s).response rho = a + s * purity rho := by
  rw [s110k_response_eq, s110k_model_eff, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, s110k_tp_trace,
    s110k_swap_trace, hr.2]
  simp [purity, Complex.mul_re]

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

theorem solution {n : ℕ} (hn : 1 ≤ n) (b : ℝ)
    (hb : 1 / (2 : ℝ) ^ n ≤ b ∧ b < 1)
    (hpure : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = 1)
    (hmixed : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = b) :
    ∀ a s : ℝ, ∃ M : ExpectationModel (Qubits n) 2,
      M.effective = (a : ℂ) • 1 + (s : ℂ) • copySwap (Qubits n) ∧
      DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
        {rho | IsDensityMatrix rho} M.response ∧
      (∀ rho, IsDensityMatrix rho → M.response rho = a + s * purity rho) ∧
      (s ≠ 0 → SeparatesPurity b M.response) := by
  intro a s
  refine ⟨s110k_model n a s, s110k_model_eff n a s, ?_, s110k_model_resp n a s, ?_⟩
  · intro V hV rho hr
    have hV' : V.conjTranspose * V = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hV
      simpa [Matrix.star_eq_conjTranspose] using this
    obtain ⟨h1, h2⟩ := s110k_density_conj V rho hV' hr
    rw [s110k_model_resp n a s _ h1, s110k_model_resp n a s _ hr, h2]
  · intro hs rho sigma hr hsg hp1 hpb heq
    rw [s110k_model_resp n a s _ hr, s110k_model_resp n a s _ hsg, hp1, hpb] at heq
    have : s * (1 - b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hs h
    · linarith [hb.2]

end
