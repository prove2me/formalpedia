-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.partialTranspose_matrix_notPositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:40:59.754885+00:00
-- url     : https://prove2.me/submissions/122d30a3-ddb1-4690-bb43-fb112966a4bf

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

lemma g52_superMatrix_id {I : Type*} [Fintype I] [DecidableEq I] :
    superMatrix (LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) = 1 := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [superMatrix, LinearMap.id_coe, id_eq, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all [Prod.ext_iff] <;> aesop

theorem solution :
    superMatrix (partialTranspose (I := Fin 2) (J := Fin 2)) =
      unreshuffleMatrix (Fin 2) (Fin 2) *
        Matrix.kronecker (superMatrix (transposeMap 2))
          (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) * reshuffleMatrix (Fin 2) (Fin 2) ∧
    ¬ (∀ X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      X.PosSemidef → (partialTranspose X).PosSemidef) := by
  constructor
  · rw [← g52_superMatrix_id, ← g52_tensorChannel]
    ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
    simp only [superMatrix]
    rw [g52_tensorMap_single]
    simp only [partialTranspose, Matrix.kronecker, Matrix.kroneckerMap_apply, transposeMap,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, Matrix.single_apply,
      Matrix.transpose_apply, Prod.mk.injEq]
    split_ifs <;> simp_all <;> aesop
  · intro h
    let Ω : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
    have hX := Matrix.posSemidef_vecMulVec_self_star Ω
    have hY := h _ hX
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hY
    let w : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
    have h2 := hY.2 w
    have : star w ⬝ᵥ (partialTranspose (Matrix.vecMulVec Ω (star Ω)) *ᵥ w) = -2 := by
      simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, w, Ω,
        partialTranspose, Matrix.vecMulVec]
      norm_num
    rw [this] at h2
    norm_num at h2
