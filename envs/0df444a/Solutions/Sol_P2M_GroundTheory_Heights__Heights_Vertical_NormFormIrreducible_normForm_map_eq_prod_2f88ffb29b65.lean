-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_map_eq_prod_2f88ffb29b65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:06.13836+00:00
-- url     : https://prove2.me/submissions/7a0ccfc0-6121-4fbd-9d8d-e6a296f4bb6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_normForm_eq_det_ab85baa4cd14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution [FiniteDimensional E L] [Algebra.IsSeparable E L] [IsAlgClosed K]
    (x : Fin n → L) :
    (normForm (R := E) L x).map (algebraMap E K) = ∏ σ : L →ₐ[E] K, embForm σ x := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable E L
  let b := pb.basis
  have hcard : Fintype.card (L →ₐ[E] K) = pb.dim := by rw [AlgHom.card, pb.finrank]
  let e : Fin pb.dim ≃ (L →ₐ[E] K) := (Fintype.equivFinOfCardEq hcard).symm
  let P := Algebra.embeddingsMatrixReindex E K b e
  have hPij : ∀ i j, P i j = e j (b i) := fun i j => by
    simp [P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hP : P.det ≠ 0 := by
    have h := (map_ne_zero (algebraMap E K)).mpr (det_traceMatrix_ne_zero' pb)
    rw [RingHom.map_det, RingHom.mapMatrix_apply,
      Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans E K b e, det_mul, det_transpose] at h
    exact left_ne_zero_of_mul h
  have hkey : ∀ (z : L) (k j : Fin pb.dim),
      ∑ i, algebraMap E K (Algebra.leftMulMatrix b z i k) * P i j = P k j * e j z := by
    intro z k j
    have h1 : z * b k = ∑ i, Algebra.leftMulMatrix b z i k • b i := by
      simp only [Algebra.leftMulMatrix_eq_repr_mul]
      exact (b.sum_repr (z * b k)).symm
    have h2 := congrArg (e j) h1
    rw [map_mul, map_sum] at h2
    simp only [hPij, Algebra.smul_def, map_mul, AlgHom.commutes] at h2 ⊢
    rw [← h2, mul_comm]
  rw [normForm_eq_det b, RingHom.map_det]
  set Λ := (MvPolynomial.map (algebraMap E K)).mapMatrix
    (∑ j, (X j : MvPolynomial (Fin n) E) •
      (Algebra.leftMulMatrix b (x j)).map (C : E →+* MvPolynomial (Fin n) E)) with hΛ
  let D : Fin pb.dim → MvPolynomial (Fin n) K := fun j => embForm (e j) x
  have hconj : Λᵀ * P.map C = P.map C * diagonal D := by
    refine Matrix.ext fun k j => ?_
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hΛ, transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_X, map_C, D, embForm]
    calc ∑ i, (∑ l, X l * C (algebraMap E K (Algebra.leftMulMatrix b (x l) i k))) * C (P i j)
        = ∑ l, X l * C (∑ i, algebraMap E K (Algebra.leftMulMatrix b (x l) i k) * P i j) := by
          simp only [Finset.sum_mul, map_sum, Finset.mul_sum, map_mul, mul_assoc]
          exact Finset.sum_comm
      _ = C (P k j) * ∑ l, X l * C (e j (x l)) := by
          simp only [hkey, Finset.mul_sum, map_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
  have hPC : (P.map C : Matrix (Fin pb.dim) (Fin pb.dim) (MvPolynomial (Fin n) K)).det = C P.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet := congrArg det hconj
  rw [det_mul, det_mul, det_transpose, det_diagonal, hPC] at hdet
  have hC : (C P.det : MvPolynomial (Fin n) K) ≠ 0 := by rwa [Ne, C_eq_zero]
  have h3 : Λ.det = ∏ j, D j := mul_right_cancel₀ hC (hdet.trans (mul_comm _ _))
  rw [h3]
  exact Equiv.prod_comp e (fun σ => embForm σ x)
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
