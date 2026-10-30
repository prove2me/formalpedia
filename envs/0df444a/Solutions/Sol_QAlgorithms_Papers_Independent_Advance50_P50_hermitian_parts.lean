-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.hermitian_parts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:57.365404+00:00
-- url     : https://prove2.me/submissions/6f86ee70-b7b5-46e5-b79c-457eb6cfe21c

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

theorem s110_tp_conjT {I : Type*} (k : ℕ) (V : Mat I) :
    tensorPower k V.conjTranspose = (tensorPower k V).conjTranspose := by
  ext a b
  simp [tensorPower, Matrix.conjTranspose_apply, star_prod]

theorem s110_lemma1_core {n k : ℕ}
    (G : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (A : Mat (Copies (Qubits n) k)) (hA : A ∈ tensorCommutant k (groupMatrices G)) :
    A.conjTranspose ∈ tensorCommutant k (groupMatrices G) := by
  classical
  unfold tensorCommutant at hA ⊢
  intro B hB
  obtain ⟨V, ⟨u, hu, rfl⟩, rfl⟩ := hB
  have h1 : (tensorPower k ((u⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Mat (Qubits n)))
      ∈ (tensorPower k) '' groupMatrices G :=
    ⟨_, ⟨u⁻¹, G.inv_mem hu, rfl⟩, rfl⟩
  have h2 := hA _ h1
  have h3 : ((u⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Mat (Qubits n))
      = (u : Mat (Qubits n)).conjTranspose := by
    rw [Matrix.UnitaryGroup.inv_apply]; rfl
  rw [h3, s110_tp_conjT] at h2
  have := congrArg Matrix.conjTranspose h2
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
  exact this.symm

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

theorem solution {n k : ℕ} (hk : 0 < k)
    (G : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ))
    (A : Mat (Copies (Qubits n) k)) (hA : A ∈ tensorCommutant k (groupMatrices G)) :
    (A + A.conjTranspose).IsHermitian ∧
    (Complex.I • (A - A.conjTranspose)).IsHermitian ∧
    A + A.conjTranspose ∈ tensorCommutant k (groupMatrices G) ∧
    Complex.I • (A - A.conjTranspose) ∈ tensorCommutant k (groupMatrices G) ∧
    (A ≠ 0 → A + A.conjTranspose ≠ 0 ∨ Complex.I • (A - A.conjTranspose) ≠ 0) := by
  classical
  have hS := s110_lemma1_core G A hA
  unfold tensorCommutant at hA hS ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_add, add_comm]
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have : star Complex.I = -Complex.I := by simp
    rw [this, neg_smul, ← smul_neg, neg_sub]
  · intro B hB
    rw [add_mul, mul_add, hA B hB, hS B hB]
  · intro B hB
    rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hA B hB, hS B hB]
  · intro h0
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have h3 : A - A.conjTranspose = 0 := by
      have := congrArg (fun X => (-Complex.I) • X) h2
      simpa [smul_smul] using this
    apply h0
    have : (2:ℂ) • A = 0 := by
      rw [two_smul]
      calc A + A = (A + A.conjTranspose) + (A - A.conjTranspose) := by abel
        _ = 0 := by rw [h1, h3, add_zero]
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero

end
