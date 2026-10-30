-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.bipartiteVectorizationTransfer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:07:19.820539+00:00
-- url     : https://prove2.me/submissions/b99691ec-a0c6-4ede-a9ab-2853a9bcbb7b

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem s109_5b_colVec_mul {a b : ℕ} (V : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin a) (Fin b) ℂ)
    (W : Matrix (Fin b) (Fin b) ℂ) :
    colVec (V * Y * W) = (Matrix.kronecker W.transpose V).mulVec (colVec Y) := by
  funext ji
  obtain ⟨j, i⟩ := ji
  simp only [colVec, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  first
  | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  | exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem s109_5b_vInner {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) ℂ) :
    vInner (colVec X) (colVec Y) = Matrix.trace (X.conjTranspose * Y) := by
  simp [vInner, colVec, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

theorem s109_5b_rankOne {ι : Type*} [Fintype ι] (x y : ι → ℂ) (U : Matrix ι ι ℂ) :
    Matrix.trace (rankOneMatrix x * U * rankOneMatrix y * U.conjTranspose) =
      (Complex.normSq (vInner x (U.mulVec y)) : ℂ) := by
  set s := vInner x (U.mulVec y) with hs
  have hR : ∀ z : ι → ℂ, ∀ a b, rankOneMatrix z a b = z a * star (z b) := by
    intro z a b; rfl
  have hent : ∀ a c, (rankOneMatrix x * U * rankOneMatrix y) a c = x a * s * star (y c) := by
    intro a c
    simp only [Matrix.mul_apply, hR, hs, vInner, Matrix.mulVec, dotProduct, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => by ring
  have hstar : star s = ∑ a, ∑ c, x a * star (y c) * star (U a c) := by
    rw [hs]
    simp only [vInner, Matrix.mulVec, dotProduct, star_sum, star_mul, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have htr : Matrix.trace (rankOneMatrix x * U * rankOneMatrix y * U.conjTranspose) =
      s * star s := by
    rw [hstar, Finset.mul_sum]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := rankOneMatrix x * U * rankOneMatrix y),
      hent, Matrix.conjTranspose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  rw [htr, Complex.normSq_eq_conj_mul_self, mul_comm]
  rfl

theorem solution {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X Y : Matrix (Fin a) (Fin b) ℂ)
    (V : Matrix.unitaryGroup (Fin a) ℂ) (W : Matrix.unitaryGroup (Fin b) ℂ) :
    colVec ((V : (Matrix (Fin a) (Fin a) ℂ)) * Y * (W : (Matrix (Fin b) (Fin b) ℂ))) =
      (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)).transpose (V : (Matrix (Fin a) (Fin a) ℂ))).mulVec (colVec Y) ∧
    vInner (colVec X) (colVec Y) = Matrix.trace (X.conjTranspose * Y) ∧
    Matrix.trace (rankOneMatrix (colVec X) * Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ)) *
      rankOneMatrix (colVec Y) * (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ))).conjTranspose) =
      (Complex.normSq (Matrix.trace (X.conjTranspose * (V : (Matrix (Fin a) (Fin a) ℂ)) * Y * (W : (Matrix (Fin b) (Fin b) ℂ)).transpose)) : ℂ) ∧
    pureStateTransfer (colVec X) (colVec Y) (Matrix.kronecker (W : (Matrix (Fin b) (Fin b) ℂ)) (V : (Matrix (Fin a) (Fin a) ℂ))) =
      Complex.normSq (vInner (colVec X) (colVec ((V : (Matrix (Fin a) (Fin a) ℂ)) * Y * (W : (Matrix (Fin b) (Fin b) ℂ)).transpose))) := by
  have key : vInner (colVec X) ((Matrix.kronecker (W : Matrix (Fin b) (Fin b) ℂ)
      (V : Matrix (Fin a) (Fin a) ℂ)).mulVec (colVec Y)) =
      Matrix.trace (X.conjTranspose * (V : Matrix (Fin a) (Fin a) ℂ) * Y *
        (W : Matrix (Fin b) (Fin b) ℂ).transpose) := by
    have h := s109_5b_colVec_mul (V : Matrix (Fin a) (Fin a) ℂ) Y
      (W : Matrix (Fin b) (Fin b) ℂ).transpose
    rw [Matrix.transpose_transpose] at h
    rw [← h, s109_5b_vInner, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  refine ⟨s109_5b_colVec_mul _ _ _, s109_5b_vInner _ _, ?_, ?_⟩
  · rw [s109_5b_rankOne, key]
  · have h := s109_5b_colVec_mul (V : Matrix (Fin a) (Fin a) ℂ) Y
      (W : Matrix (Fin b) (Fin b) ℂ).transpose
    rw [Matrix.transpose_transpose] at h
    rw [h, pureStateTransfer, s109_5b_rankOne]
    simp

end
