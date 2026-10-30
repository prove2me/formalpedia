-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.proposition3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:59:03.470951+00:00
-- url     : https://prove2.me/submissions/09a6fabd-b91e-4104-92d7-b1ca49d61d7a

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

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

theorem solution {n k : ℕ} (hk : 0 < k) (M : ExpectationModel (Qubits n) k)
    (G : Bool → Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (R : Bool → Set (Mat (Qubits n))) (label : Mat (Qubits n) → Bool)
    (hdata : ∀ i, DatasetSymmetry (groupMatrices (G i)) (R i) label) :
    ((∀ i, M.effective ∈ tensorCommutant k (groupMatrices (G i))) →
      ∀ i, DomainInvariant (groupMatrices (G i)) (R i) M.response) ∧
    (∀ i, M.effective ∈ tensorCommutant k (groupMatrices (G i)) →
      M.effective ∉ tensorCommutant k (groupMatrices (G (!i))) →
      DomainInvariant (groupMatrices (G i)) (R i) M.response) :=
  ⟨fun h i => s110k_invariant M (G i) (R i) (h i),
   fun i h _ => s110k_invariant M (G i) (R i) h⟩

end
