-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P41.spectralTrace
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-04T20:13:02.328564+00:00
-- url     : https://prove2.me/submissions/68f64f3f-171c-4b46-ae85-0cb249f7e474

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators
open Matrix

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- `linearRankOneMatrix v φ` is the outer product of the column `v` with the row
`(φ(e_j))_j`. -/
lemma linearRankOneMatrix_eq_col_mul_row {d : ℕ} (v : Fin d → ℂ)
    (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) :
    linearRankOneMatrix v phi =
      replicateCol Unit v * replicateRow Unit (fun j => phi (Pi.single j 1)) := by
  ext i j
  simp [linearRankOneMatrix, replicateCol, replicateRow, Matrix.mul_apply]

/-- A linear functional on `Fin d → ℂ` is the dot product with its values on the
standard basis. -/
lemma phi_apply_eq_dotProduct {d : ℕ} (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) (x : Fin d → ℂ) :
    phi x = (fun j => phi (Pi.single j 1)) ⬝ᵥ x := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (x j) : Fin d → ℂ) = x j • (Pi.single j (1 : ℂ) : Fin d → ℂ) := by
    rw [← Pi.single_smul']; simp
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- `Tr(vφ) = φ(v)`. -/
lemma trace_linearRankOneMatrix {d : ℕ} (v : Fin d → ℂ) (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) :
    trace (linearRankOneMatrix v phi) = phi v := by
  rw [phi_apply_eq_dotProduct, dotProduct, trace]
  simp [linearRankOneMatrix, mul_comm]

/-- Matrix determinant lemma: `det(M + vφ) = det M · (1 + φ(M⁻¹ v))`. -/
lemma det_add_linearRankOneMatrix {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.det ≠ 0)
    (v : Fin d → ℂ) (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) :
    (M + linearRankOneMatrix v phi).det = M.det * (1 + phi (M⁻¹ *ᵥ v)) := by
  rw [linearRankOneMatrix_eq_col_mul_row,
    det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hM)]
  congr 1
  rw [Matrix.det_unique, phi_apply_eq_dotProduct]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- The resolvent scalar as a ratio of determinants. -/
lemma resolventScalar_eq_det_div {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) (t : ℂ)
    (h : (t • (1 : Matrix (Fin d) (Fin d) ℂ) - A).det ≠ 0) :
    resolventScalar A v phi t =
      (t • (1 : Matrix (Fin d) (Fin d) ℂ) - A + linearRankOneMatrix v phi).det /
        (t • (1 : Matrix (Fin d) (Fin d) ℂ) - A).det := by
  rw [det_add_linearRankOneMatrix _ h, resolventScalar, mul_div_cancel_left₀ _ h]

/-- A matrix with an eigenbasis is conjugate to the diagonal matrix of its eigenvalues. -/
lemma exists_conj_diagonal_of_eigenbasis {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (b : Module.Basis (Fin d) ℂ (Fin d → ℂ)) (lam : Fin d → ℂ)
    (hb : ∀ i, M *ᵥ b i = lam i • b i) :
    ∃ B : Matrix (Fin d) (Fin d) ℂ, IsUnit B ∧ B⁻¹ * M * B = diagonal lam := by
  let B : Matrix (Fin d) (Fin d) ℂ := (Pi.basisFun ℂ (Fin d)).toMatrix b
  have hB : IsUnit B :=
    @isUnit_of_invertible _ _ B (Module.Basis.invertibleToMatrix (Pi.basisFun ℂ (Fin d)) b)
  have hMB : M * B = B * diagonal lam := by
    ext i j
    have := congr_fun (hb j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [B, Module.Basis.toMatrix_apply, Matrix.mul_apply, this, diagonal_apply, mul_comm]
  refine ⟨B, hB, ?_⟩
  rw [Matrix.mul_assoc, hMB, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det B).mp hB), Matrix.one_mul]

/-- With an eigenbasis, `det(tI - M) = ∏ (t - λᵢ)`. -/
lemma det_sub_eq_prod_of_eigenbasis {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (b : Module.Basis (Fin d) ℂ (Fin d → ℂ)) (lam : Fin d → ℂ)
    (hb : ∀ i, M *ᵥ b i = lam i • b i) (t : ℂ) :
    (t • (1 : Matrix (Fin d) (Fin d) ℂ) - M).det = ∏ i, (t - lam i) := by
  obtain ⟨B, hB, h⟩ := exists_conj_diagonal_of_eigenbasis M b lam hb
  rw [← det_conj' hB (t • (1 : Matrix (Fin d) (Fin d) ℂ) - M), Matrix.mul_sub, Matrix.sub_mul, h,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det B).mp hB)]
  rw [show t • (1 : Matrix (Fin d) (Fin d) ℂ) - diagonal lam = diagonal (fun i => t - lam i) by
    ext i j; by_cases hij : i = j <;> simp [hij, Matrix.one_apply]]
  exact det_diagonal

/-- With an eigenbasis, `Tr M = ∑ λᵢ`. -/
lemma trace_eq_sum_of_eigenbasis {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (b : Module.Basis (Fin d) ℂ (Fin d → ℂ)) (lam : Fin d → ℂ)
    (hb : ∀ i, M *ᵥ b i = lam i • b i) :
    trace M = ∑ i, lam i := by
  obtain ⟨B, hB, h⟩ := exists_conj_diagonal_of_eigenbasis M b lam hb
  rw [← trace_conj' hB M, h, trace_diagonal]

end QAlgorithms.Papers.Independent.Intakenext100.P41

open QAlgorithms.Papers.Independent.Intakenext100.P41

theorem solution {d : ℕ} (A : BasicODEData d) :
    (∑ i, A.lambda i) - (∑ i, A.mu i) = A.phi A.v ∧
      A.phi A.v = Matrix.trace (linearRankOneMatrix A.v A.phi) := by
  have h1 := trace_eq_sum_of_eigenbasis A.P A.xi A.lambda A.eigenP
  have h2 := trace_eq_sum_of_eigenbasis _ A.zeta A.mu A.eigenPminusQ
  refine ⟨?_, (trace_linearRankOneMatrix A.v A.phi).symm⟩
  rw [← h1, ← h2, trace_sub, sub_sub_cancel, trace_linearRankOneMatrix]
