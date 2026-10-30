-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:23.877874+00:00
-- url     : https://prove2.me/submissions/16b09d6b-ec32-490b-95e5-b509f0d6271b

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
    A.conjTranspose ∈ tensorCommutant k (groupMatrices G) :=
  s110_lemma1_core G A hA

end
