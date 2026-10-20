-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.tensorChannel_matrix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:40:39.838017+00:00
-- url     : https://prove2.me/submissions/5e94c71d-f654-4b71-9929-98116132b666

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct
open QAlgorithms.Papers.Independent.Frontier18.P17
open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)
open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

lemma g52_unres_mul {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {R : Type*} (M : Matrix ((I × I) × (J × J)) R ℂ) (p : (I × J) × (I × J)) (r : R) :
    (unreshuffleMatrix I J * M) p r = M ((p.1.1, p.2.1), (p.1.2, p.2.2)) r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((p.1.1, p.2.1), (p.1.2, p.2.2))]
  · simp [unreshuffleMatrix]
  · intro q _ hq
    have : p ≠ ((q.1.1, q.2.1), (q.1.2, q.2.2)) := by
      rintro rfl; exact hq rfl
    simp [unreshuffleMatrix, this]
  · simp

lemma g52_mul_res {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {R : Type*} (M : Matrix R ((I × I) × (J × J)) ℂ) (q : R) (s : (I × J) × (I × J)) :
    (M * reshuffleMatrix I J) q s = M q ((s.1.1, s.2.1), (s.1.2, s.2.2)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((s.1.1, s.2.1), (s.1.2, s.2.2))]
  · simp [reshuffleMatrix]
  · intro r _ hr
    simp [reshuffleMatrix, hr]
  · simp

lemma g52_tensorMap_single {I J K L : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (F : Matrix I I ℂ →ₗ[ℂ] Matrix K K ℂ) (G : Matrix J J ℂ →ₗ[ℂ] Matrix L L ℂ) (i i' : I) (j j' : J) :
    tensorMap F G (Matrix.single (i, j) (i', j') 1) =
      Matrix.kronecker (F (Matrix.single i i' 1)) (G (Matrix.single j j' 1)) := by
  unfold tensorMap
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Finset.sum_eq_single i', Finset.sum_eq_single j']
  · simp
  all_goals first
    | (intro x _ hx; simp [Matrix.single_apply, hx, Ne.symm hx])
    | simp
    | (intro x _ hx; refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => ?_;
       simp [Matrix.single_apply, hx, Ne.symm hx])
    | (intro x _ hx; refine Finset.sum_eq_zero fun y _ => ?_;
       simp [Matrix.single_apply, hx, Ne.symm hx])
    | (intro x _ hx; refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ =>
         Finset.sum_eq_zero fun w _ => ?_;
       simp [Matrix.single_apply, hx, Ne.symm hx])

theorem g52_tensorChannel {m n : ℕ}
    (Phi : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (Psi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    superMatrix (tensorMap Phi Psi) = unreshuffleMatrix (Fin m) (Fin n) *
      Matrix.kronecker (superMatrix Phi) (superMatrix Psi) * reshuffleMatrix (Fin m) (Fin n) := by
  ext p s
  rw [g52_mul_res, g52_unres_mul]
  simp only [superMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [g52_tensorMap_single]
  rfl

theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (Phi : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (Psi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hPhi : CPTP Phi) (hPsi : CPTP Psi) :
    superMatrix (tensorMap Phi Psi) = unreshuffleMatrix (Fin m) (Fin n) *
      Matrix.kronecker (superMatrix Phi) (superMatrix Psi) * reshuffleMatrix (Fin m) (Fin n) :=
  g52_tensorChannel Phi Psi
