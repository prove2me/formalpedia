-- Prove2me | solution 1 for QuadMatIneq.Stabilization.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T15:38:00.503439+00:00
-- url     : https://prove2.me/submissions/df6f8f37-b11c-4a0a-a706-9fe9091529c9

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_QuadMatIneq_Stabilization_Data
import Definitions.Def_QuadMatIneq_Stabilization_QMI
import Mathlib



section

open Matrix
open scoped BigOperators

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def qform (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

@[simp] theorem qform_zero (M : Matrix ι ι ℝ) : qform M 0 = 0 := by
  simp [qform]

theorem qform_smul (M : Matrix ι ι ℝ) (a : ℝ) (x : ι → ℝ) :
    qform M (a • x) = a ^ 2 * qform M x := by
  simp only [qform, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem qform_add (M : Matrix ι ι ℝ) (x y : ι → ℝ) :
    qform M (x + y) = qform M x + x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x) + qform M y := by
  simp only [qform, mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem qform_matrix_add (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    qform (M + N) x = qform M x + qform N x := by
  simp [qform, add_mulVec, dotProduct_add]

theorem qform_matrix_sub (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    qform (M - N) x = qform M x - qform N x := by
  simp [qform, sub_mulVec, dotProduct_sub]

theorem qform_matrix_smul (a : ℝ) (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    qform (a • M) x = a * qform M x := by
  simp [qform, smul_mulVec, dotProduct_smul]

theorem continuous_qform (M : Matrix ι ι ℝ) : Continuous (qform M) := by
  unfold qform dotProduct mulVec
  fun_prop

theorem qform_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (x : ι → ℝ) :
    0 ≤ qform M x := by
  simpa [qform] using hM.dotProduct_mulVec_nonneg x

theorem qform_pos {M : Matrix ι ι ℝ} (hM : M.PosDef) {x : ι → ℝ} (hx : x ≠ 0) :
    0 < qform M x := by
  simpa [qform] using hM.dotProduct_mulVec_pos hx

theorem posSemidef_of_qform {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (h : ∀ x, 0 ≤ qform M x) : M.PosSemidef := by
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM (by simpa [qform] using h)

theorem posDef_of_qform {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (h : ∀ x, x ≠ 0 → 0 < qform M x) : M.PosDef := by
  exact Matrix.PosDef.of_dotProduct_mulVec_pos hM (by simpa [qform] using h)

theorem qform_congr (M : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (x : κ → ℝ) :
    qform (Bᵀ * M * B) x = qform M (B *ᵥ x) := by
  simp only [qform, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix
open scoped BigOperators

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem qmi_qform (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) (x : ι → ℝ) :
    qform (qmiForm N Z) x = qform N (Sum.elim x (Z *ᵥ x)) := by
  rw [qmiForm, qform_congr]
  congr 1
  simp [Matrix.fromRows_mulVec]

omit [DecidableEq ι] [DecidableEq κ] in
theorem qform_blocks (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    qform (Matrix.fromBlocks A B C D) (Sum.elim x y) =
      qform A x + x ⬝ᵥ (B *ᵥ y) + y ⬝ᵥ (C *ᵥ x) + qform D y := by
  simp only [qform, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, dotProduct_add]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem qform_blocks_self (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    qform N (Sum.elim x y) = qform N.toBlocks₁₁ x + x ⬝ᵥ (N.toBlocks₁₂ *ᵥ y) +
      y ⬝ᵥ (N.toBlocks₂₁ *ᵥ x) + qform N.toBlocks₂₂ y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks N]
  exact qform_blocks _ _ _ _ _ _

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem hermitian_cross (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hN : N.IsHermitian) :
    N.toBlocks₂₁ = N.toBlocks₁₂ᵀ := by
  ext i j
  have h := congrFun (congrFun hN (Sum.inl j)) (Sum.inr i)
  change N (Sum.inr i) (Sum.inl j) = N (Sum.inl j) (Sum.inr i)
  simpa using h

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix


namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m T : ℕ}

def systemGraph (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin m)) (Fin n) ℝ := Matrix.fromRows 1 (Matrix.fromRows Aᵀ Bᵀ)

theorem data_factor_graph (X : Matrix (Fin n) (Fin (T+1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    (dataFactor3 X Um)ᵀ * systemGraph A B =
      Matrix.fromRows 1 (Xplus X-A*Xminus X-B*Um)ᵀ := by
  unfold dataFactor3 systemGraph
  rw [Matrix.fromBlocks_transpose,Matrix.transpose_one,Matrix.transpose_zero,
    Matrix.transpose_neg,Matrix.transpose_fromRows]
  rw [Matrix.fromBlocks_mul_fromRows (1 : Matrix (Fin n) (Fin n) ℝ)
    (Matrix.fromRows Aᵀ Bᵀ)]
  simp only [Matrix.zero_mul,add_zero,Matrix.mul_one,Matrix.neg_mul,
    Matrix.fromCols_mul_fromRows]
  congr 1
  rw [Matrix.transpose_sub,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_mul]
  abel

theorem native_data_qmi (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    qmiForm (Nmat Φ X Um) (Matrix.fromRows Aᵀ Bᵀ) =
      qmiForm Φ (Xplus X-A*Xminus X-B*Um)ᵀ := by
  let R : Matrix (Fin n ⊕ (Fin n ⊕ Fin m)) (Fin n) ℝ := systemGraph A B
  let S : Matrix (Fin n ⊕ Fin T) (Fin n) ℝ :=
    Matrix.fromRows 1 (Xplus X-A*Xminus X-B*Um)ᵀ
  let D := dataFactor3 X Um
  change Rᵀ*(D*Φ*Dᵀ)*R=Sᵀ*Φ*S
  have h : Dᵀ*R=S := data_factor_graph X Um A B
  rw [←h,Matrix.transpose_mul,Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

theorem sigma_iff_native_qmi (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A,B)∈Sigma Φ X Um ↔ (qmiForm (Nmat Φ X Um) (Matrix.fromRows Aᵀ Bᵀ)).PosSemidef := by
  rw [native_data_qmi]
  constructor
  · rintro ⟨W,hW,hpos⟩
    have he : Xplus X-A*Xminus X-B*Um=W := by rw [hW]; abel
    simpa [he,ZSet] using hpos
  · intro h
    refine ⟨Xplus X-A*Xminus X-B*Um, ?_, h⟩
    abel

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι : Type*} [Fintype ι]

theorem hermitian_bilinear_symm {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have hs : Mᵀ = M := by simpa [Matrix.IsHermitian] using hM
  simpa [hs] using Matrix.dotProduct_transpose_mulVec M x y

theorem qform_add_smul {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (x y : ι → ℝ) (t : ℝ) :
    qform M (x + t • y) = qform M x + 2 * t * (x ⬝ᵥ (M *ᵥ y)) + t^2*qform M y := by
  rw [qform_add, qform_smul]
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hermitian_bilinear_symm hM y x]
  ring

theorem quadratic_cauchy_schwarz {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    (x y : ι → ℝ) : (x ⬝ᵥ (M *ᵥ y))^2 ≤ qform M x * qform M y := by
  have hd := discrim_le_zero (a := qform M y)
    (b := 2*(x ⬝ᵥ (M *ᵥ y))) (c := qform M x) (fun t : ℝ => by
      have h := qform_nonneg hM (x + t • y)
      rw [qform_add_smul hM.isHermitian] at h
      nlinarith)
  dsimp [discrim] at hd
  nlinarith

theorem qform_zero_iff {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (x : ι → ℝ) :
    qform M x = 0 ↔ M *ᵥ x = 0 := by
  simpa [qform] using hM.dotProduct_mulVec_zero_iff x

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

def dataTransform (Φ : Matrix (ι ⊕ τ) (ι ⊕ τ) ℝ)
    (F : Matrix ι τ ℝ) (D : Matrix κ τ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  let B : Matrix (ι ⊕ κ) (ι ⊕ τ) ℝ := Matrix.fromBlocks 1 F 0 (-D)
  B * Φ * Bᵀ

omit [Fintype κ] [DecidableEq κ] [DecidableEq τ] in
theorem dataTransform_blocks (Φ : Matrix (ι ⊕ τ) (ι ⊕ τ) ℝ)
    (F : Matrix ι τ ℝ) (D : Matrix κ τ ℝ) :
    (dataTransform Φ F D).toBlocks₂₂=D*Φ.toBlocks₂₂*Dᵀ ∧
    (dataTransform Φ F D).toBlocks₁₂=-(Φ.toBlocks₁₂+F*Φ.toBlocks₂₂)*Dᵀ := by
  constructor
  all_goals
    unfold dataTransform
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Φ]
    simp [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply]
  all_goals
    rw [←Matrix.neg_mul]
    congr 1
    abel

omit [DecidableEq κ] [DecidableEq τ] in
theorem dataTransform_geometry (Φ : Matrix (ι ⊕ τ) (ι ⊕ τ) ℝ)
    (F : Matrix ι τ ℝ) (D : Matrix κ τ ℝ)
    (hΦ : Φ.IsHermitian) (hG : (-Φ.toBlocks₂₂).PosSemidef)
    (hker : ∀ v, Φ.toBlocks₂₂*ᵥv=0 → Φ.toBlocks₁₂*ᵥv=0) :
    (dataTransform Φ F D).IsHermitian ∧
    (-(dataTransform Φ F D).toBlocks₂₂).PosSemidef ∧
    ∀ v, (dataTransform Φ F D).toBlocks₂₂*ᵥv=0 →
      (dataTransform Φ F D).toBlocks₁₂*ᵥv=0 := by
  have hsym : (dataTransform Φ F D).IsHermitian := by
    simpa [dataTransform] using Matrix.isHermitian_mul_mul_conjTranspose
      (Matrix.fromBlocks 1 F 0 (-D)) hΦ
  obtain ⟨h22,h12⟩ := dataTransform_blocks Φ F D
  have hpos : (-(dataTransform Φ F D).toBlocks₂₂).PosSemidef := by
    rw [h22]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_neg,
      Matrix.neg_mul] using hG.mul_mul_conjTranspose_same D
  refine ⟨hsym,hpos,?_⟩
  intro v hv
  have hz : qform (-Φ.toBlocks₂₂) (Dᵀ*ᵥv)=0 := by
    rw [←qform_congr]
    have he : Dᵀᵀ*(-Φ.toBlocks₂₂)*Dᵀ=-(dataTransform Φ F D).toBlocks₂₂ := by
      rw [Matrix.transpose_transpose,h22,Matrix.mul_neg,Matrix.neg_mul]
    rw [he]
    apply (qform_zero_iff hpos v).2
    simpa only [Matrix.neg_mulVec,neg_eq_zero] using hv
  have hg := (qform_zero_iff hG (Dᵀ*ᵥv)).1 hz
  have hg' : Φ.toBlocks₂₂*ᵥ(Dᵀ*ᵥv)=0 := by
    simpa only [Matrix.neg_mulVec,neg_eq_zero] using hg
  have hk := hker _ hg'
  rw [h12,←Matrix.mulVec_mulVec,Matrix.neg_mulVec,Matrix.add_mulVec,
    ←Matrix.mulVec_mulVec,hg',hk,Matrix.mulVec_zero,add_zero,neg_zero]

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m : ℕ}

def feedbackGraph (K : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n ⊕ Fin m) (Fin n) ℝ :=
  Matrix.fromRows 1 K

theorem Mmat_factor (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) :
    Mmat P K = Matrix.fromBlocks P 0 0
      (-(feedbackGraph K * P * (feedbackGraph K)ᵀ)) := by
  simp [Mmat, feedbackGraph, Matrix.fromRows_mul, Matrix.transpose_fromRows,
    Matrix.fromBlocks_neg, Matrix.mul_assoc]

theorem Mmat_geometry (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (hP : P.PosDef) : (Mmat P K).IsHermitian ∧ (-(Mmat P K).toBlocks₂₂).PosSemidef := by
  rw [Mmat_factor]
  have hr := hP.posSemidef.mul_mul_conjTranspose_same (feedbackGraph K)
  have hr' : (feedbackGraph K * P * (feedbackGraph K)ᵀ).PosSemidef := by
    simpa using hr
  constructor
  · exact Matrix.IsHermitian.fromBlocks hP.isHermitian (by simp) hr'.isHermitian.neg
  · simpa using hr'

theorem Mmat_qmi (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    qmiForm (Mmat P K) (Matrix.fromRows Aᵀ Bᵀ) =
      P-(A+B*K)*P*(A+B*K)ᵀ := by
  simp only [qmiForm,Mmat,Matrix.transpose_fromRows,Matrix.transpose_one,
    Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows,
    Matrix.one_mul,Matrix.mul_one,Matrix.mul_zero,zero_add,add_zero,
    Matrix.mul_neg,Matrix.transpose_transpose,
    Matrix.transpose_add,Matrix.transpose_mul]
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.neg_mul,Matrix.mul_assoc]
  abel

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem full_rank_transpose_injective (D : Matrix ι κ ℝ)
    (hr : D.rank=Fintype.card ι) : Function.Injective Dᵀ.mulVec := by
  have hs : Function.Surjective D.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hr
  intro x y hxy
  have hz : ∀ z : ι → ℝ, z⬝ᵥx=z⬝ᵥy := by
    intro z
    obtain ⟨v,hv⟩ := hs z
    change D*ᵥv=z at hv
    calc
      z⬝ᵥx = x⬝ᵥ(D*ᵥv) := by rw [hv,dotProduct_comm]
      _ = v⬝ᵥ(Dᵀ*ᵥx) := (Matrix.dotProduct_transpose_mulVec D v x).symm
      _ = v⬝ᵥ(Dᵀ*ᵥy) := by rw [hxy]
      _ = z⬝ᵥy := by rw [Matrix.dotProduct_transpose_mulVec,hv,dotProduct_comm]
  have h := hz (x-y)
  have hsq : (x-y)⬝ᵥ(x-y)=0 := by rw [dotProduct_sub,h,sub_self]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hsq)

omit [DecidableEq ι] [DecidableEq κ] in
theorem full_rank_congruence_posDef (G : Matrix κ κ ℝ) (D : Matrix ι κ ℝ)
    (hG : G.PosDef) (hr : D.rank=Fintype.card ι) : (D*G*Dᵀ).PosDef := by
  simpa using hG.conjTranspose_mul_mul_same (full_rank_transpose_injective D hr)

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix
namespace QuadMatIneq.Stabilization.QMIFresh
variable {n m T : ℕ}

theorem native_N_geometry
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : InPi Φ) :
    (Nmat Φ X Um).IsHermitian ∧ (-(Nmat Φ X Um).toBlocks₂₂).PosSemidef ∧
      ∀ v, (Nmat Φ X Um).toBlocks₂₂ *ᵥ v = 0 →
        (Nmat Φ X Um).toBlocks₁₂ *ᵥ v = 0 := by
  exact dataTransform_geometry Φ (Xplus X) (Matrix.fromRows (Xminus X) Um)
    hΦ.1 hΦ.2.1 hΦ.2.2.2

theorem native_N_feasible
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hgen : ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ B : Matrix (Fin n) (Fin m) ℝ,
      (A,B) ∈ Sigma Φ X Um) :
    ∃ Z : Matrix (Fin n ⊕ Fin m) (Fin n) ℝ, (qmiForm (Nmat Φ X Um) Z).PosSemidef := by
  obtain ⟨A,B,hAB⟩ := hgen
  exact ⟨Matrix.fromRows Aᵀ Bᵀ, (sigma_iff_native_qmi Φ X Um A B).mp hAB⟩

theorem native_all_Z_implication
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ AB ∈ Sigma Φ X Um,
      (P-(AB.1+AB.2*K)*P*(AB.1+AB.2*K)ᵀ).PosDef) :
    ∀ Z, (qmiForm (Nmat Φ X Um) Z).PosSemidef → (qmiForm (Mmat P K) Z).PosDef := by
  intro Z hZ
  have he : Matrix.fromRows Z.toRows₁ᵀᵀ Z.toRows₂ᵀᵀ = Z := by
    simp only [Matrix.transpose_transpose, Matrix.fromRows_toRows]
  have hAB : (Z.toRows₁ᵀ, Z.toRows₂ᵀ) ∈ Sigma Φ X Um := by
    apply (sigma_iff_native_qmi Φ X Um _ _).mpr
    rwa [he]
  have hm := h (Z.toRows₁ᵀ, Z.toRows₂ᵀ) hAB
  rw [←he, Mmat_qmi]
  exact hm

theorem native_N_lower_posDef
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : (-Φ.toBlocks₂₂).PosDef)
    (hr : (Matrix.fromRows (Xminus X) Um).rank = n+m) :
    (-(Nmat Φ X Um).toBlocks₂₂).PosDef := by
  have h22 := (dataTransform_blocks Φ (Xplus X) (Matrix.fromRows (Xminus X) Um)).1
  change (-(dataTransform Φ (Xplus X) (Matrix.fromRows (Xminus X) Um)).toBlocks₂₂).PosDef
  rw [h22]
  have hr' : (Matrix.fromRows (Xminus X) Um).rank = Fintype.card (Fin n ⊕ Fin m) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hr
  simpa only [Matrix.mul_neg, Matrix.neg_mul] using
    full_rank_congruence_posDef (-Φ.toBlocks₂₂) (Matrix.fromRows (Xminus X) Um) hΦ hr'

end QuadMatIneq.Stabilization.QMIFresh
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Matrix Set
variable {ι : Type*} [Fintype ι]

def squareNorm (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

theorem squareNorm_nonneg (x : ι → ℝ) : 0 ≤ squareNorm x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

@[simp] theorem squareNorm_zero : squareNorm (0 : ι → ℝ) = 0 := by simp [squareNorm]

theorem squareNorm_pos {x : ι → ℝ} (hx : x ≠ 0) : 0 < squareNorm x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    simpa using not_exists.mp h i
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem squareNorm_smul (a : ℝ) (x : ι → ℝ) : squareNorm (a • x) = a ^ 2 * squareNorm x := by
  simp only [squareNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem qform_one [DecidableEq ι] (x : ι → ℝ) : qform (1 : Matrix ι ι ℝ) x = squareNorm x := by
  simp [qform, squareNorm, dotProduct, pow_two]

theorem continuous_squareNorm : Continuous (squareNorm : (ι → ℝ) → ℝ) := by
  unfold squareNorm
  fun_prop

theorem squareNorm_unit_compact : IsCompact {x : ι → ℝ | squareNorm x = 1} := by
  apply (isCompact_closedBall (0 : ι → ℝ) 1).of_isClosed_subset
    (isClosed_eq continuous_squareNorm continuous_const)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro i
  have hi : x i ^ 2 ≤ squareNorm x := Finset.single_le_sum
    (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  change squareNorm x = 1 at hx
  rw [hx] at hi
  change |x i| ≤ 1
  nlinarith [sq_abs (x i), abs_nonneg (x i)]

theorem squareNorm_normalize {x : ι → ℝ} (hx : x ≠ 0) :
    squareNorm ((Real.sqrt (squareNorm x))⁻¹ • x) = 1 := by
  rw [squareNorm_smul]
  have he := squareNorm_pos hx
  have hs := Real.sq_sqrt he.le
  have hp : Real.sqrt (squareNorm x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 he)
  rw [inv_pow]
  calc
    _ = (Real.sqrt (squareNorm x) ^ 2)⁻¹ * (Real.sqrt (squareNorm x) ^ 2) :=
      congrArg (fun t : ℝ => (Real.sqrt (squareNorm x) ^ 2)⁻¹ * t) hs.symm
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hp)

theorem quadratic_strict_unit_margin (M N : Matrix ι ι ℝ)
    (himp : ∀ x, x ≠ 0 → 0 ≤ qform N x → 0 < qform M x)
    (hne : ∃ x : ι → ℝ, x ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ x, squareNorm x = 1 →
      -(d / 2) ≤ qform N x → d ≤ qform M x := by
  let F : (ι → ℝ) → ℝ := fun x => max (-qform N x) (qform M x)
  have hF : Continuous F := (continuous_qform N).neg.max (continuous_qform M)
  have hnonempty : Set.Nonempty {x : ι → ℝ | squareNorm x = 1} := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, squareNorm_normalize hx⟩
  obtain ⟨z, hz, hmin⟩ := squareNorm_unit_compact.exists_isMinOn hnonempty hF.continuousOn
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hpos : 0 < F z := by
    by_cases hN : 0 ≤ qform N z
    · exact lt_of_lt_of_le (himp z hz0 hN) (le_max_right _ _)
    · exact lt_of_lt_of_le (by linarith : 0 < -qform N z) (le_max_left _ _)
  refine ⟨F z, hpos, ?_⟩
  intro x hx hN
  have hle := hmin hx
  change F z ≤ max (-qform N x) (qform M x) at hle
  rcases le_max_iff.mp hle with h | h
  · linarith
  · exact h

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m T : ℕ}

theorem dataFactor4_mulVec (X : Matrix (Fin n) (Fin (T+1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (x y : Fin n → ℝ) (z : Fin m → ℝ)
    (w : Fin n → ℝ) :
    (dataFactor4 X Um)ᵀ *ᵥ Sum.elim (Sum.elim x y) (Sum.elim z w) =
      Sum.elim x ((Xplus X)ᵀ*ᵥx-(Xminus X)ᵀ*ᵥy-Umᵀ*ᵥz) := by
  ext i
  cases i <;> simp [dataFactor4, Matrix.transpose_fromRows, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_mulVec,Matrix.neg_mulVec,sub_eq_add_neg,add_assoc]

theorem dataFactor3_mulVec (X : Matrix (Fin n) (Fin (T+1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (x y : Fin n → ℝ) (z : Fin m → ℝ) :
    (dataFactor3 X Um)ᵀ *ᵥ Sum.elim x (Sum.elim y z) =
      Sum.elim x ((Xplus X)ᵀ*ᵥx-(Xminus X)ᵀ*ᵥy-Umᵀ*ᵥz) := by
  ext i
  cases i <;> simp [dataFactor3, Matrix.transpose_fromRows, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_mulVec,Matrix.neg_mulVec,sub_eq_add_neg,add_assoc]

theorem lmi55_qform (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ)
    (x y : Fin n → ℝ) (z : Fin m → ℝ) (w : Fin n → ℝ) :
    qform (lmi55 Φ X Um P L β) (Sum.elim (Sum.elim x y) (Sum.elim z w)) =
      qform P x-β*squareNorm x-qform P y-2*(z⬝ᵥ(L*ᵥy))+
      2*(z⬝ᵥ(L*ᵥw))+qform P w-
      qform Φ (Sum.elim x ((Xplus X)ᵀ*ᵥx-(Xminus X)ᵀ*ᵥy-Umᵀ*ᵥz)) := by
  rw [lmi55,qform_matrix_sub]
  have he : qform (dataFactor4 X Um*Φ*(dataFactor4 X Um)ᵀ)
      (Sum.elim (Sum.elim x y) (Sum.elim z w)) =
      qform Φ (Sum.elim x ((Xplus X)ᵀ*ᵥx-(Xminus X)ᵀ*ᵥy-Umᵀ*ᵥz)) := by
    simpa only [Matrix.transpose_transpose, dataFactor4_mulVec] using
      qform_congr Φ (dataFactor4 X Um)ᵀ (Sum.elim (Sum.elim x y) (Sum.elim z w))
  rw [he,qform_blocks,qform_blocks,qform_blocks,qform_matrix_sub,
    qform_matrix_smul,qform_one]
  simp only [qform, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.neg_mulVec, Matrix.zero_mulVec, dotProduct_zero,
    sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_neg,
    Matrix.dotProduct_transpose_mulVec]
  ring

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem qform_sub_null (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (u v : ι → ℝ) (hv : M*ᵥv=0) : qform M (u-v)=qform M u := by
  have hcross : v⬝ᵥ(M*ᵥu)=0 := by rw [hermitian_bilinear_symm hM,hv,dotProduct_zero]
  simp only [qform,Matrix.mulVec_sub,hv,sub_zero,sub_dotProduct,hcross,sub_zero]

omit [DecidableEq ι] [DecidableEq κ] in
theorem vertical_null (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (v : κ → ℝ)
    (h₁ : M.toBlocks₁₂*ᵥv=0) (h₂ : M.toBlocks₂₂*ᵥv=0) :
    M*ᵥSum.elim 0 v=0 := by
  conv_lhs => rw [←Matrix.fromBlocks_toBlocks M]
  simp [Matrix.fromBlocks_mulVec,h₁,h₂]

def verticalMatrix (K : Matrix κ κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks 0 0 0 K

omit [DecidableEq ι] [DecidableEq κ] in
theorem vertical_qform (K : Matrix κ κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    qform (verticalMatrix K) (Sum.elim x y)=qform K y := by
  rw [verticalMatrix,qform_blocks]
  simp [qform]

omit [DecidableEq ι] [DecidableEq κ] in
theorem vertical_posSemidef (K : Matrix κ κ ℝ) (hK : K.PosSemidef) :
    (verticalMatrix (ι:=ι) K).PosSemidef := by
  apply posSemidef_of_qform (Matrix.IsHermitian.fromBlocks (by simp) (by simp) hK.isHermitian)
  intro v
  change 0 ≤ qform (verticalMatrix K) v
  have he : v=Sum.elim (v∘Sum.inl) (v∘Sum.inr) := by ext i; cases i <;> rfl
  rw [he,vertical_qform]
  exact qform_nonneg hK _

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix
namespace QuadMatIneq.Stabilization.QMIFresh
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def topMatrix : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.fromBlocks 1 0 0 0

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem topMatrix_hermitian : (topMatrix (ι:=ι) (κ:=κ)).IsHermitian :=
  Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one (by simp) (by simp)

omit [DecidableEq κ] in
theorem topMatrix_qform (x : ι → ℝ) (y : κ → ℝ) :
    qform (topMatrix (ι:=ι) (κ:=κ)) (Sum.elim x y)=squareNorm x := by
  rw [topMatrix,qform_blocks]
  simp [qform,squareNorm,dotProduct,pow_two]

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m T : ℕ}

theorem Mmat_qform (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (x y : Fin n → ℝ) (z : Fin m → ℝ) :
    qform (Mmat P K) (Sum.elim x (Sum.elim y z)) = qform P x-qform P (y+Kᵀ*ᵥz) := by
  rw [Mmat_factor,feedbackGraph,qform_blocks]
  have he := qform_congr P (Matrix.fromRows 1 K)ᵀ (Sum.elim y z)
  simp only [Matrix.transpose_fromRows,
    Matrix.transpose_one,Matrix.fromCols_mulVec_sumElim,Matrix.one_mulVec] at he
  simp only [Matrix.zero_mulVec,dotProduct_zero,add_zero]
  have hneg : qform (-(Matrix.fromRows 1 K*P*(Matrix.fromRows 1 K)ᵀ)) (Sum.elim y z) =
      -qform (Matrix.fromRows 1 K*P*(Matrix.fromRows 1 K)ᵀ) (Sum.elim y z) := by
    simp only [qform,Matrix.neg_mulVec,dotProduct_neg]
  have he' : qform (Matrix.fromRows 1 K*P*(Matrix.fromRows 1 K)ᵀ) (Sum.elim y z) =
      qform P (y+Kᵀ*ᵥz) := by
    simpa only [Matrix.transpose_fromRows, Matrix.transpose_fromCols,
      Matrix.transpose_one, Matrix.transpose_transpose] using he
  rw [hneg,he']
  rfl

theorem lmi55_hermitian (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ)
    (hΦ : Φ.IsHermitian) (hP : P.IsHermitian) : (lmi55 Φ X Um P L β).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · apply Matrix.IsHermitian.fromBlocks
    · exact Matrix.IsHermitian.fromBlocks
        (hP.sub (Matrix.isHermitian_one.smul (by rfl))) (by simp) hP.neg
    · simp [Matrix.fromBlocks_transpose]
    · exact Matrix.IsHermitian.fromBlocks (by simp) (by simp) hP
  · simpa using Matrix.isHermitian_mul_mul_conjTranspose (dataFactor4 X Um) hΦ

theorem lmi55_complete_square (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (β : ℝ)
    (hP : P.IsHermitian) (x y : Fin n → ℝ) (z : Fin m → ℝ) (w : Fin n → ℝ) :
    qform (lmi55 Φ X Um P (K*P) β) (Sum.elim (Sum.elim x y) (Sum.elim z w)) =
      qform (Mmat P K-Nmat Φ X Um-β•topMatrix) (Sum.elim x (Sum.elim y z))+
      qform P (w+Kᵀ*ᵥz) := by
  rw [lmi55_qform,qform_matrix_sub,qform_matrix_sub,qform_matrix_smul,topMatrix_qform,Mmat_qform]
  have hn := qform_congr Φ (dataFactor3 X Um)ᵀ (Sum.elim x (Sum.elim y z))
  simp only [Matrix.transpose_transpose,dataFactor3_mulVec] at hn
  change qform (Nmat Φ X Um) (Sum.elim x (Sum.elim y z))=_ at hn
  rw [hn,qform_add,qform_add]
  have hy : y⬝ᵥ(P*ᵥ(Kᵀ*ᵥz))=z⬝ᵥ((K*P)*ᵥy) := by
    rw [hermitian_bilinear_symm hP,dotProduct_comm (Kᵀ*ᵥz) (P*ᵥy),
      Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec]
  have hw : w⬝ᵥ(P*ᵥ(Kᵀ*ᵥz))=z⬝ᵥ((K*P)*ᵥw) := by
    rw [hermitian_bilinear_symm hP,dotProduct_comm (Kᵀ*ᵥz) (P*ᵥw),
      Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec]
  rw [hy,hw,hermitian_bilinear_symm hP (Kᵀ*ᵥz) y,
    hermitian_bilinear_symm hP (Kᵀ*ᵥz) w,hy,hw]
  ring

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m T : ℕ}

theorem Nmat_hermitian (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : Φ.IsHermitian) : (Nmat Φ X Um).IsHermitian := by
  simpa [Nmat] using Matrix.isHermitian_mul_mul_conjTranspose (dataFactor3 X Um) hΦ

theorem lmi55_iff_certificate (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (β : ℝ)
    (hΦ : Φ.IsHermitian) (hP : P.PosDef) :
    (lmi55 Φ X Um P (K*P) β).PosSemidef ↔
      (Mmat P K-Nmat Φ X Um-β•topMatrix).PosSemidef := by
  have hs : (Mmat P K-Nmat Φ X Um-β•topMatrix).IsHermitian :=
    ((Mmat_geometry P K hP).1.sub (Nmat_hermitian Φ X Um hΦ)).sub
    (topMatrix_hermitian.smul (by rfl))
  constructor
  · intro h
    apply posSemidef_of_qform hs
    intro v
    let x := v∘Sum.inl
    let y := v∘Sum.inr∘Sum.inl
    let z := v∘Sum.inr∘Sum.inr
    have he : v=Sum.elim x (Sum.elim y z) := by
      ext i
      rcases i with i|i
      · rfl
      · cases i <;> rfl
    have hh := qform_nonneg h (Sum.elim (Sum.elim x y) (Sum.elim z (-(Kᵀ*ᵥz))))
    rw [lmi55_complete_square _ _ _ _ _ _ hP.isHermitian,neg_add_cancel,qform_zero,add_zero,←he] at hh
    exact hh
  · intro h
    apply posSemidef_of_qform (lmi55_hermitian Φ X Um P (K*P) β hΦ hP.isHermitian)
    intro v
    let x := v∘Sum.inl∘Sum.inl
    let y := v∘Sum.inl∘Sum.inr
    let z := v∘Sum.inr∘Sum.inl
    let w := v∘Sum.inr∘Sum.inr
    have he : v=Sum.elim (Sum.elim x y) (Sum.elim z w) := by
      ext i; rcases i with i|i <;> cases i <;> rfl
    rw [he,lmi55_complete_square _ _ _ _ _ _ hP.isHermitian]
    exact add_nonneg (qform_nonneg h _) (qform_nonneg hP.posSemidef _)

theorem lmi56_eq_lmi55_zero (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) :
    lmi56 Φ X Um P L=lmi55 Φ X Um P L 0 := by simp [lmi56,lmi55]

theorem lmi56_iff_certificate (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (hΦ : Φ.IsHermitian) (hP : P.PosDef) :
    (lmi56 Φ X Um P (K*P)).PosDef ↔ (Mmat P K-Nmat Φ X Um).PosDef := by
  rw [lmi56_eq_lmi55_zero]
  have hs := (Mmat_geometry P K hP).1.sub (Nmat_hermitian Φ X Um hΦ)
  constructor
  · intro h
    apply posDef_of_qform hs
    intro v hv
    let x := v∘Sum.inl
    let y := v∘Sum.inr∘Sum.inl
    let z := v∘Sum.inr∘Sum.inr
    have he : v=Sum.elim x (Sum.elim y z) := by
      ext i
      rcases i with i|i
      · rfl
      · cases i <;> rfl
    have hne : Sum.elim (Sum.elim x y) (Sum.elim z (-(Kᵀ*ᵥz)))≠0 := by
      intro hh
      apply hv
      rw [he]
      ext i
      rcases i with i|i
      · exact congrFun hh (Sum.inl (Sum.inl i))
      · rcases i with i|i
        · exact congrFun hh (Sum.inl (Sum.inr i))
        · exact congrFun hh (Sum.inr (Sum.inl i))
    have hh := qform_pos h hne
    rw [lmi55_complete_square _ _ _ _ _ _ hP.isHermitian,neg_add_cancel,qform_zero,
      add_zero,zero_smul,sub_zero,←he] at hh
    exact hh
  · intro h
    apply posDef_of_qform (lmi55_hermitian Φ X Um P (K*P) 0 hΦ hP.isHermitian)
    intro v hv
    let x := v∘Sum.inl∘Sum.inl
    let y := v∘Sum.inl∘Sum.inr
    let z := v∘Sum.inr∘Sum.inl
    let w := v∘Sum.inr∘Sum.inr
    have he : v=Sum.elim (Sum.elim x y) (Sum.elim z w) := by
      ext i; rcases i with i|i <;> cases i <;> rfl
    rw [he,lmi55_complete_square _ _ _ _ _ _ hP.isHermitian,zero_smul,sub_zero]
    by_cases hu : Sum.elim x (Sum.elim y z)=0
    · have hx : x=0 := congrArg (fun u : Fin n ⊕ (Fin n ⊕ Fin m) → ℝ => u∘Sum.inl) hu
      have hy : y=0 := congrArg (fun u : Fin n ⊕ (Fin n ⊕ Fin m) → ℝ => u∘Sum.inr∘Sum.inl) hu
      have hz : z=0 := congrArg (fun u : Fin n ⊕ (Fin n ⊕ Fin m) → ℝ => u∘Sum.inr∘Sum.inr) hu
      have hw : w≠0 := by intro hw; apply hv; rw [he,hx,hy,hz,hw]; ext i; rcases i with i|i <;> cases i <;> rfl
      rw [hu,qform_zero,hz,Matrix.mulVec_zero,add_zero,zero_add]
      exact qform_pos hP hw
    · exact add_pos_of_pos_of_nonneg (qform_pos h hu) (qform_nonneg hP.posSemidef _)

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m T : ℕ}

theorem Mmat_smul (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (a : ℝ) :
    Mmat (a•P) K=a•Mmat P K := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · simp [Mmat]
  · simp [Mmat]
  · rcases i with i|i <;> rcases j with j|j <;>
      simp [Mmat,Matrix.mul_smul,Matrix.smul_mul]

theorem margin_coefficient_pos (P : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n ⊕ (Fin n ⊕ Fin m))
      (Fin n ⊕ (Fin n ⊕ Fin m)) ℝ) (α β : ℝ) (hn : 0<n)
    (hP : P.PosDef) (hα : 0≤α)
    (hc : (Mmat P K-α•N-β•topMatrix).PosSemidef) : 0<α := by
  by_contra h
  have he : α=0 := le_antisymm (le_of_not_gt h) hα
  let y : Fin n → ℝ := Pi.single ⟨0,hn⟩ 1
  have hy : y≠0 := by intro hh; have he := congrFun hh ⟨0,hn⟩; simp [y] at he
  have hh := qform_nonneg hc (Sum.elim 0 (Sum.elim y 0))
  rw [qform_matrix_sub,qform_matrix_sub,qform_matrix_smul,qform_matrix_smul,
    Mmat_qform,topMatrix_qform,he,zero_mul,qform_zero,squareNorm_zero,
    Matrix.mulVec_zero,add_zero,mul_zero,sub_zero] at hh
  have hp := qform_pos hP hy
  linarith

theorem scale_margin_certificate (P : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n ⊕ (Fin n ⊕ Fin m))
      (Fin n ⊕ (Fin n ⊕ Fin m)) ℝ) (α β : ℝ) (hα : 0<α)
    (hc : (Mmat P K-α•N-β•topMatrix).PosSemidef) :
    (Mmat (α⁻¹•P) K-N-(α⁻¹*β)•topMatrix).PosSemidef := by
  have h := hc.smul (inv_pos.mpr hα).le
  have he : α⁻¹•(Mmat P K-α•N-β•topMatrix)=
      Mmat (α⁻¹•P) K-N-(α⁻¹*β)•topMatrix := by
    rw [Mmat_smul,smul_sub,smul_sub,smul_smul,smul_smul,inv_mul_cancel₀ (ne_of_gt hα),one_smul]
  rwa [he] at h

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {m T : ℕ}

theorem zero_state_margin (N : Matrix (Fin 0 ⊕ (Fin 0 ⊕ Fin m))
    (Fin 0 ⊕ (Fin 0 ⊕ Fin m)) ℝ) (hN : N.IsHermitian)
    (hG : (-N.toBlocks₂₂).PosSemidef) :
    (Mmat (1 : Matrix (Fin 0) (Fin 0) ℝ) (0 : Matrix (Fin m) (Fin 0) ℝ)-N-
      (1:ℝ)•topMatrix).PosSemidef := by
  have hP : (1 : Matrix (Fin 0) (Fin 0) ℝ).PosDef := Matrix.PosDef.one
  apply posSemidef_of_qform
    (((Mmat_geometry _ _ hP).1.sub hN).sub (topMatrix_hermitian.smul (by rfl)))
  intro v
  let z : Fin m → ℝ := v∘Sum.inr∘Sum.inr
  have he : v=Sum.elim (0 : Fin 0 → ℝ) (Sum.elim (0 : Fin 0 → ℝ) z) := by
    ext i
    rcases i with i|i
    · exact Fin.elim0 i
    · rcases i with i|i
      · exact Fin.elim0 i
      · rfl
  rw [he,qform_matrix_sub,qform_matrix_sub,qform_matrix_smul,Mmat_qform,
    topMatrix_qform,qform_blocks_self]
  have hh := qform_nonneg hG (Sum.elim 0 z)
  simp only [qform,Matrix.neg_mulVec,dotProduct_neg] at hh
  simpa [qform, squareNorm] using hh

theorem zero_state_strict (N : Matrix (Fin 0 ⊕ (Fin 0 ⊕ Fin m))
    (Fin 0 ⊕ (Fin 0 ⊕ Fin m)) ℝ) (hN : N.IsHermitian)
    (hG : (-N.toBlocks₂₂).PosDef) :
    (Mmat (1 : Matrix (Fin 0) (Fin 0) ℝ) (0 : Matrix (Fin m) (Fin 0) ℝ)-N).PosDef := by
  have hP : (1 : Matrix (Fin 0) (Fin 0) ℝ).PosDef := Matrix.PosDef.one
  apply posDef_of_qform ((Mmat_geometry _ _ hP).1.sub hN)
  intro v hv
  let z : Fin m → ℝ := v∘Sum.inr∘Sum.inr
  have he : v=Sum.elim (0 : Fin 0 → ℝ) (Sum.elim (0 : Fin 0 → ℝ) z) := by
    ext i
    rcases i with i|i
    · exact Fin.elim0 i
    · rcases i with i|i
      · exact Fin.elim0 i
      · rfl
  have hb : (Sum.elim 0 z : Fin 0 ⊕ Fin m → ℝ)≠0 := by
    intro h
    apply hv
    rw [he,h]
    ext i
    cases i <;> rfl
  rw [he,qform_matrix_sub,Mmat_qform,qform_blocks_self]
  have hh := qform_pos hG hb
  simp only [qform,Matrix.neg_mulVec,dotProduct_neg] at hh
  simpa [qform] using hh

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

 theorem linear_factor_of_kernel {E F H : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (f : E →ₗ[ℝ] F) (g : E →ₗ[ℝ] H) (h : f.ker ≤ g.ker) :
    ∃ a : F →ₗ[ℝ] H, a.comp f = g := by
  let a₀ : f.range →ₗ[ℝ] H := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨a, ha⟩ := a₀.exists_extend
  refine ⟨a, ?_⟩
  ext x
  have hx := LinearMap.congr_fun ha ⟨f x, LinearMap.mem_range_self f x⟩
  simpa [a₀] using hx

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

omit [Fintype τ] in
 theorem matrix_factor_of_kernel (G : Matrix κ ι ℝ) (B : Matrix τ ι ℝ)
    (h : ∀ x, G *ᵥ x = 0 → B *ᵥ x = 0) : ∃ F : Matrix τ κ ℝ, F * G = B := by
  classical
  obtain ⟨f, hf⟩ := linear_factor_of_kernel G.mulVecLin B.mulVecLin h
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  exact LinearMap.congr_fun hf x

omit [Fintype ι] in
 theorem center_exists (G : Matrix κ κ ℝ) (B : Matrix ι κ ℝ)
    (hG : G.IsHermitian) (h : ∀ x, G *ᵥ x = 0 → B *ᵥ x = 0) :
    ∃ C : Matrix κ ι ℝ, G * C = Bᵀ := by
  obtain ⟨F, hF⟩ := matrix_factor_of_kernel G B h
  refine ⟨Fᵀ, ?_⟩
  have hs : Gᵀ = G := by simpa [Matrix.IsHermitian] using hG
  simpa [Matrix.transpose_mul, hs] using congrArg Matrix.transpose hF

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem complete_square (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (G : Matrix κ κ ℝ)
    (C : Matrix κ ι ℝ) (hG : G.IsHermitian) (hC : G * C = Bᵀ)
    (x : ι → ℝ) (y : κ → ℝ) :
    qform (Matrix.fromBlocks A B Bᵀ (-G)) (Sum.elim x y) =
      qform (A + B*C) x - qform G (y - C *ᵥ x) := by
  have hCx : G *ᵥ (C *ᵥ x) = Bᵀ *ᵥ x := by rw [Matrix.mulVec_mulVec, hC]
  have hc1 : (C *ᵥ x) ⬝ᵥ (G *ᵥ y) = x ⬝ᵥ (B *ᵥ y) := by
    rw [hermitian_bilinear_symm hG, hCx, Matrix.dotProduct_transpose_mulVec]
  have hc2 : (C *ᵥ x) ⬝ᵥ (G *ᵥ (C *ᵥ x)) = x ⬝ᵥ ((B*C) *ᵥ x) := by
    rw [hCx, Matrix.dotProduct_transpose_mulVec, ← Matrix.mulVec_mulVec]
  rw [qform_blocks, qform_matrix_add]
  simp only [qform, Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_sub,
    sub_dotProduct, dotProduct_sub]
  rw [hc1, hc2, hCx]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem centered_form_exists (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hN : N.IsHermitian) (hker : ∀ v, N.toBlocks₂₂ *ᵥ v = 0 → N.toBlocks₁₂ *ᵥ v = 0) :
    ∃ C : Matrix κ ι ℝ,
      (-N.toBlocks₂₂) * C = N.toBlocks₁₂ᵀ ∧
      ∀ x y, qform N (Sum.elim x y) =
        qform (N.toBlocks₁₁ + N.toBlocks₁₂*C) x - qform (-N.toBlocks₂₂) (y-C*ᵥ x) := by
  have hG : (-N.toBlocks₂₂).IsHermitian := (hN.submatrix Sum.inr).neg
  obtain ⟨C, hC⟩ := center_exists (-N.toBlocks₂₂) N.toBlocks₁₂ hG (by
    intro v hv
    apply hker
    simpa only [Matrix.neg_mulVec, neg_eq_zero] using hv)
  refine ⟨C, hC, ?_⟩
  intro x y
  have he : N = Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₁₂ᵀ (-(-N.toBlocks₂₂)) := by
    rw [neg_neg, ← hermitian_cross N hN, Matrix.fromBlocks_toBlocks]
  conv_lhs => rw [he]
  exact complete_square _ _ _ _ hG hC x y

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem outer_mulVec (d : κ → ℝ) (ell z : ι → ℝ) :
    (fun i j => d i * ell j) *ᵥ z = (ell ⬝ᵥ z) • d := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rank_one_interpolation (S : Matrix ι ι ℝ) (G : Matrix κ κ ℝ)
    (hS : S.PosSemidef) (hG : G.PosSemidef) (x : ι → ℝ) (d : κ → ℝ)
    (hx : x ≠ 0) (hd : qform G d ≤ qform S x) :
    ∃ T : Matrix κ ι ℝ, T *ᵥ x = d ∧ ∀ z, qform G (T *ᵥ z) ≤ qform S z := by
  have hs := qform_nonneg hS x
  by_cases ht : qform S x = 0
  · have hgd : qform G d = 0 := le_antisymm (hd.trans_eq ht) (qform_nonneg hG d)
    have hxx : x ⬝ᵥ x ≠ 0 := mt dotProduct_self_eq_zero.mp hx
    let ell : ι → ℝ := (x ⬝ᵥ x)⁻¹ • x
    refine ⟨fun i j => d i * ell j, ?_, ?_⟩
    · rw [outer_mulVec]
      have he : ell ⬝ᵥ x = 1 := by simp [ell, smul_dotProduct, hxx]
      rw [he, one_smul]
    · intro z
      rw [outer_mulVec, qform_smul, hgd, mul_zero]
      exact qform_nonneg hS z
  · have htpos : 0 < qform S x := lt_of_le_of_ne hs (Ne.symm ht)
    let ell : ι → ℝ := (qform S x)⁻¹ • (S *ᵥ x)
    refine ⟨fun i j => d i * ell j, ?_, ?_⟩
    · rw [outer_mulVec]
      have he : ell ⬝ᵥ x = 1 := by
        dsimp [ell]
        rw [smul_dotProduct, dotProduct_comm]
        change (qform S x)⁻¹ * qform S x = 1
        exact inv_mul_cancel₀ ht
      rw [he, one_smul]
    · intro z
      rw [outer_mulVec, qform_smul]
      have he : ell ⬝ᵥ z = (x ⬝ᵥ (S *ᵥ z)) / qform S x := by
        dsimp [ell]
        rw [smul_dotProduct, dotProduct_comm, hermitian_bilinear_symm hS.isHermitian z x]
        simp [div_eq_mul_inv, mul_comm]
      rw [he]
      have hc := quadratic_cauchy_schwarz hS x z
      have hnum : (x ⬝ᵥ (S *ᵥ z))^2 * qform G d ≤
          qform S z * (qform S x)^2 := by
        calc
          _ ≤ (x ⬝ᵥ (S *ᵥ z))^2 * qform S x := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
          _ ≤ (qform S x * qform S z) * qform S x := mul_le_mul_of_nonneg_right hc hs
          _ = _ := by ring
      calc
        _ = ((x ⬝ᵥ (S *ᵥ z))^2 * qform G d) / (qform S x)^2 := by ring
        _ ≤ qform S z := (div_le_iff₀ (sq_pos_of_pos htpos)).2 hnum

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem center_schur_hermitian (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (G : Matrix κ κ ℝ) (C : Matrix κ ι ℝ)
    (hA : A.IsHermitian) (hG : G.IsHermitian) (hC : G*C=Bᵀ) :
    (A+B*C).IsHermitian := by
  have hs : Gᵀ=G := by simpa [Matrix.IsHermitian] using hG
  have hb : B=Cᵀ*G := by
    have ht := congrArg Matrix.transpose hC
    simpa [Matrix.transpose_mul, hs] using ht.symm
  apply hA.add
  rw [hb]
  have ht : (Cᵀ*G*C)ᵀ=Cᵀ*G*C := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs]
    exact (Matrix.mul_assoc _ _ _).symm
  simpa [Matrix.IsHermitian] using ht

theorem centered_schur_nonneg (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hN : N.IsHermitian) (hG : (-N.toBlocks₂₂).PosSemidef)
    (C : Matrix κ ι ℝ) (hC : (-N.toBlocks₂₂)*C=N.toBlocks₁₂ᵀ)
    (hc : ∀ x y, qform N (Sum.elim x y) =
      qform (N.toBlocks₁₁+N.toBlocks₁₂*C) x-qform (-N.toBlocks₂₂) (y-C*ᵥx))
    (Z : Matrix κ ι ℝ) (hZ : (qmiForm N Z).PosSemidef) :
    (N.toBlocks₁₁+N.toBlocks₁₂*C).PosSemidef := by
  apply posSemidef_of_qform (center_schur_hermitian _ _ _ _
    (hN.submatrix Sum.inl) hG.isHermitian hC)
  intro x
  change 0 ≤ qform (N.toBlocks₁₁+N.toBlocks₁₂*C) x
  have hz := qform_nonneg hZ x
  rw [qmi_qform, hc] at hz
  have hg := qform_nonneg hG (Z*ᵥx-C*ᵥx)
  linarith

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem feasible_interpolation (N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hN : N.IsHermitian) (hG : (-N.toBlocks₂₂).PosSemidef)
    (hker : ∀ v, N.toBlocks₂₂ *ᵥ v = 0 → N.toBlocks₁₂ *ᵥ v = 0)
    (Z₀ : Matrix κ ι ℝ) (hZ₀ : (qmiForm N Z₀).PosSemidef)
    (x : ι → ℝ) (y : κ → ℝ) (hx : x ≠ 0)
    (hxy : 0 ≤ qform N (Sum.elim x y)) :
    ∃ Z : Matrix κ ι ℝ, Z *ᵥ x = y ∧ (qmiForm N Z).PosSemidef := by
  obtain ⟨C, hC, hc⟩ := centered_form_exists N hN hker
  have hS := centered_schur_nonneg N hN hG C hC hc Z₀ hZ₀
  have hd : qform (-N.toBlocks₂₂) (y-C*ᵥx) ≤
      qform (N.toBlocks₁₁+N.toBlocks₁₂*C) x := by
    rw [hc] at hxy
    linarith
  obtain ⟨T, hTx, hT⟩ := rank_one_interpolation _ _ hS hG x (y-C*ᵥx) hx hd
  refine ⟨C+T, ?_, ?_⟩
  · rw [Matrix.add_mulVec, hTx]
    abel
  · apply posSemidef_of_qform
      (by simpa [qmiForm] using Matrix.isHermitian_conjTranspose_mul_mul (Matrix.fromRows 1 (C+T)) hN)
    intro z
    rw [qmi_qform, hc, Matrix.add_mulVec]
    have he : C*ᵥz+T*ᵥz-C*ᵥz=T*ᵥz := by abel
    rw [he]
    exact sub_nonneg.mpr (hT z)

end QuadMatIneq.Stabilization.QMIFresh
end


section

namespace QuadMatIneq.Stabilization.QMIFresh

theorem quadratic_nonneg_leading (a b c : ℝ)
    (h : ∀ t : ℝ, 0 ≤ a*t^2+b*t+c) : 0 ≤ a := by
  by_contra ha
  have ha' : a < 0 := lt_of_not_ge ha
  have hc : 0 ≤ c := by simpa using h 0
  let t := c / (-a) + 1
  have ht : 1 ≤ t := by
    have hh : 0 ≤ c / (-a) := div_nonneg hc (neg_nonneg.mpr ha'.le)
    dsimp [t]
    linarith
  have he : (-a)*(t-1)=c := by dsimp [t]; field_simp [ne_of_lt ha']; ring
  have hp := h t
  have hm := h (-t)
  have hsq : t ≤ t^2 := by nlinarith
  have hmul := mul_le_mul_of_nonpos_left hsq ha'.le
  nlinarith

theorem affine_nonneg_slope (b c : ℝ) (h : ∀ t : ℝ, 0 ≤ b*t+c) : b=0 := by
  by_contra hb
  have hh := h (-(c+1)/b)
  have he : b*(-(c+1)/b)+c = -1 := by field_simp; ring
  rw [he] at hh
  norm_num at hh

theorem quadratic_rigidity (a b c : ℝ) (ha : a ≤ 0)
    (h : ∀ t : ℝ, 0 ≤ a*t^2+b*t+c) : a=0 ∧ b=0 := by
  have he : a=0 := le_antisymm ha (quadratic_nonneg_leading a b c h)
  refine ⟨he, affine_nonneg_slope b c ?_⟩
  intro t
  simpa [he] using h t

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem kernel_annihilation (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hMneg : (-M.toBlocks₂₂).PosSemidef) (hG : (-N.toBlocks₂₂).PosSemidef)
    (hker : ∀ v, N.toBlocks₂₂ *ᵥ v = 0 → N.toBlocks₁₂ *ᵥ v = 0)
    (Z₀ : Matrix κ ι ℝ) (hZ₀ : (qmiForm N Z₀).PosSemidef)
    (himp : ∀ Z, (qmiForm N Z).PosSemidef → (qmiForm M Z).PosDef)
    (hne : ∃ x : ι → ℝ, x ≠ 0) :
    ∀ v, N.toBlocks₂₂ *ᵥ v = 0 →
      M.toBlocks₂₂ *ᵥ v = 0 ∧ M.toBlocks₁₂ *ᵥ v = 0 := by
  obtain ⟨C, hC, hc⟩ := centered_form_exists N hN hker
  have hS := centered_schur_nonneg N hN hG C hC hc Z₀ hZ₀
  intro v hv
  let w : ι ⊕ κ → ℝ := Sum.elim 0 v
  have hGw : (-N.toBlocks₂₂)*ᵥv=0 := by rw [Matrix.neg_mulVec,hv,neg_zero]
  have hwq : qform M w = qform M.toBlocks₂₂ v := by
    simp [w, qform_blocks_self, qform_zero]
  have hnonpos : qform M w ≤ 0 := by
    have hh := qform_nonneg hMneg v
    rw [hwq]
    simpa only [qform, Matrix.neg_mulVec, dotProduct_neg, neg_nonneg] using hh
  have hpoly : ∀ x : ι → ℝ, x ≠ 0 →
      qform M w=0 ∧ (Sum.elim x (C*ᵥx)) ⬝ᵥ (M*ᵥw)=0 := by
    intro x hx
    let u : ι ⊕ κ → ℝ := Sum.elim x (C*ᵥx)
    have hall : ∀ t : ℝ, 0 ≤ qform M (u+t•w) := by
      intro t
      have he : u+t•w=Sum.elim x (C*ᵥx+t•v) := by
        ext i
        cases i <;> simp [u,w]
      rw [he]
      have hnq : 0 ≤ qform N (Sum.elim x (C*ᵥx+t•v)) := by
        rw [hc]
        have hy : C*ᵥx+t•v-C*ᵥx=t•v := by abel
        rw [hy,qform_smul]
        have hz : qform (-N.toBlocks₂₂) v=0 := (qform_zero_iff hG v).2 hGw
        rw [hz,mul_zero,sub_zero]
        exact qform_nonneg hS x
      obtain ⟨Z,hZx,hZ⟩ := feasible_interpolation N hN hG hker Z₀ hZ₀ x
        (C*ᵥx+t•v) hx hnq
      have hm := (qform_pos (himp Z hZ) hx).le
      rwa [qmi_qform,hZx] at hm
    have hp := quadratic_rigidity (qform M w) (2*(u⬝ᵥ(M*ᵥw))) (qform M u)
      hnonpos (fun t => by have ht := hall t; rw [qform_add_smul hM] at ht; nlinarith)
    exact ⟨hp.1, by change u⬝ᵥ(M*ᵥw)=0; linarith [hp.2]⟩
  obtain ⟨x,hx⟩ := hne
  have hm22 : M.toBlocks₂₂*ᵥv=0 := by
    have hzero : qform (-M.toBlocks₂₂) v=0 := by
      change v ⬝ᵥ ((-M.toBlocks₂₂)*ᵥv)=0
      rw [Matrix.neg_mulVec,dotProduct_neg]
      change -qform M.toBlocks₂₂ v=0
      rw [←hwq,(hpoly x hx).1,neg_zero]
    have hh := (qform_zero_iff hMneg v).1 hzero
    simpa only [Matrix.neg_mulVec,neg_eq_zero] using hh
  refine ⟨hm22, ?_⟩
  by_contra hb
  have hh := (hpoly (M.toBlocks₁₂*ᵥv) hb).2
  have he : M*ᵥw=Sum.elim (M.toBlocks₁₂*ᵥv) 0 := by
    conv_lhs => rw [←Matrix.fromBlocks_toBlocks M]
    simp [w,Matrix.fromBlocks_mulVec,hm22]
  rw [he,sumElim_dotProduct_sumElim,dotProduct_zero,add_zero] at hh
  exact hb (dotProduct_self_eq_zero.mp hh)

end QuadMatIneq.Stabilization.QMIFresh
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Matrix Unitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_kernel_projector (G : Matrix ι ι ℝ) (hG : G.IsHermitian) :
    ∃ K : Matrix ι ι ℝ, K.IsHermitian ∧ K * K = K ∧ G * K = 0 ∧ K * G = 0 ∧
      (∀ v, G *ᵥ v = 0 → K *ᵥ v = v) ∧ K.PosSemidef ∧
      (∀ v, qform K v = squareNorm (K *ᵥ v)) := by
  let e := conjStarAlgAut ℝ (Matrix ι ι ℝ) hG.eigenvectorUnitary
  let lam := hG.eigenvalues
  let p : ι → ℝ := fun i => if lam i = 0 then 1 else 0
  let r : ι → ℝ := fun i => if lam i = 0 then 0 else (lam i)⁻¹
  let K := e (diagonal p)
  let R := e (diagonal r)
  have hdiag : G = e (diagonal lam) := hG.spectral_theorem
  have hp : (diagonal p).IsHermitian := Matrix.isHermitian_diagonal p
  have hK : K.IsHermitian := (hp.isSelfAdjoint.map e).isHermitian
  have hKK : K * K = K := by
    dsimp [K]
    rw [← map_mul, diagonal_mul_diagonal]
    apply congrArg e
    apply congrArg diagonal
    funext i
    by_cases h : lam i = 0 <;> simp [p, h]
  have hGK : G * K = 0 := by
    rw [hdiag]
    change e (diagonal lam) * e (diagonal p) = 0
    rw [← map_mul, diagonal_mul_diagonal]
    have hzero : (fun i => lam i * p i) = 0 := by
      funext i
      by_cases h : lam i = 0 <;> simp [p, h]
    rw [hzero, diagonal_zero', map_zero]
  have hKG : K * G = 0 := by
    have h := congrArg star hGK
    simpa only [star_mul, hK.star_eq, hG.star_eq, star_zero] using h
  have hrel : K + R * G = 1 := by
    rw [hdiag]
    change e (diagonal p) + e (diagonal r) * e (diagonal lam) = 1
    rw [← map_mul, diagonal_mul_diagonal, ← map_add, diagonal_add]
    have he : (fun i => p i + r i * lam i) = (fun _ => 1) := by
      funext i
      by_cases h : lam i = 0 <;> simp [p, r, h]
    rw [he, diagonal_one, map_one]
  have hfix : ∀ v, G *ᵥ v = 0 → K *ᵥ v = v := by
    intro v hv
    have h := congrArg (fun A : Matrix ι ι ℝ => A *ᵥ v) hrel
    simpa only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, add_zero, one_mulVec] using h
  have hnorm : ∀ v, qform K v = squareNorm (K *ᵥ v) := by
    intro v
    have ht : Kᵀ = K := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hK
    calc
      qform K v = qform (Kᵀ * (1 : Matrix ι ι ℝ) * K) v := by rw [ht, mul_one, hKK]
      _ = qform (1 : Matrix ι ι ℝ) (K *ᵥ v) := qform_congr _ _ _
      _ = _ := qform_one _
  refine ⟨K, hK, hKK, hGK, hKG, hfix, posSemidef_of_qform hK ?_, hnorm⟩
  intro v
  rw [hnorm]
  exact squareNorm_nonneg _

theorem psd_kernel_projector (G : Matrix ι ι ℝ) (hG : G.PosSemidef) :
    ∃ K : Matrix ι ι ℝ, K.IsHermitian ∧ K * K = K ∧ G * K = 0 ∧ K * G = 0 ∧
      (∀ v, G *ᵥ v = 0 → K *ᵥ v = v) ∧ K.PosSemidef ∧
      (∀ v, qform K v = squareNorm (K *ᵥ v)) ∧
      (∀ v, qform G v = 0 → K *ᵥ v = 0 → v = 0) := by
  obtain ⟨K, hK, hKK, hGK, hKG, hfix, hpos, hnorm⟩ := hermitian_kernel_projector G hG.isHermitian
  refine ⟨K, hK, hKK, hGK, hKG, hfix, hpos, hnorm, ?_⟩
  intro v hq hk
  have hv := (qform_zero_iff hG v).mp hq
  exact (hfix v hv).symm.trans hk

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

noncomputable section

namespace QuadMatIneq.Stabilization.QMIFresh

open Set

def detPair (a b : ℝ × ℝ) : ℝ := a.1 * b.2 - a.2 * b.1

theorem detPair_eq_zero_collinear {a b : ℝ × ℝ} (hb : b ≠ 0)
    (h : detPair a b = 0) : ∃ c : ℝ, a = c • b := by
  by_cases hb1 : b.1 = 0
  · have hb2 : b.2 ≠ 0 := by
      intro h2
      apply hb
      exact Prod.ext hb1 h2
    refine ⟨a.2 / b.2, ?_⟩
    apply Prod.ext
    · change a.1 = a.2 / b.2 * b.1
      have ha : a.1 = 0 := by
        simp only [detPair, hb1, mul_zero, sub_zero] at h
        exact (mul_eq_zero.mp h).resolve_right hb2
      simp [ha, hb1]
    · change a.2 = a.2 / b.2 * b.2
      field_simp
  · refine ⟨a.1 / b.1, ?_⟩
    apply Prod.ext
    · change a.1 = a.1 / b.1 * b.1
      field_simp
    · change a.2 = a.1 / b.1 * b.2
      dsimp [detPair] at h
      field_simp
      linarith

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (Q : V → ℝ × ℝ)

theorem quadratic_range_smul (hscale : ∀ (r : ℝ) v, Q (r • v) = r ^ 2 • Q v)
    {a : ℝ × ℝ} (ha : a ∈ Set.range Q) {r : ℝ} (hr : 0 ≤ r) :
    r • a ∈ Set.range Q := by
  obtain ⟨v, rfl⟩ := ha
  refine ⟨Real.sqrt r • v, ?_⟩
  rw [hscale, Real.sq_sqrt hr]

theorem quadratic_range_add (hzero : Q 0 = 0) (hcont : Continuous Q)
    (hscale : ∀ (r : ℝ) v, Q (r • v) = r ^ 2 • Q v)
    (hrot : ∀ (u v : V) (t : ℝ),
      Q (Real.cos t • u + Real.sin t • v) +
        Q (-Real.sin t • u + Real.cos t • v) = Q u + Q v)
    (u v : V) : Q u + Q v ∈ Set.range Q := by
  let w := Q u + Q v
  by_cases hw : w = 0
  · exact ⟨0, hzero.trans hw.symm⟩
  let f : ℝ → ℝ := fun t => detPair (Q (Real.cos t • u + Real.sin t • v)) w
  have hf : Continuous f := by
    dsimp [f, detPair]
    fun_prop
  have hfpi : f (Real.pi / 2) = -f 0 := by
    simp only [f, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul,
      zero_add, Real.cos_zero, Real.sin_zero, add_zero]
    dsimp [detPair, w]
    ring
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hex : ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), f t = 0 := by
    by_cases h : f 0 ≤ 0
    · exact intermediate_value_Icc hpi hf.continuousOn ⟨h, by rw [hfpi]; linarith⟩
    · exact intermediate_value_Icc' hpi hf.continuousOn ⟨by rw [hfpi]; linarith, le_of_lt (lt_of_not_ge h)⟩
  obtain ⟨t, _, ht⟩ := hex
  let x := Real.cos t • u + Real.sin t • v
  let y := -Real.sin t • u + Real.cos t • v
  obtain ⟨c, hc⟩ := detPair_eq_zero_collinear hw ht
  have hx : Q x = c • w := hc
  have hy : Q y = (1 - c) • w := by
    have h := hrot u v t
    change Q x + Q y = w at h
    rw [hx] at h
    apply Prod.ext
    · have h1 := congrArg Prod.fst h
      change c * w.1 + (Q y).1 = w.1 at h1
      change (Q y).1 = (1 - c) * w.1
      linarith
    · have h2 := congrArg Prod.snd h
      change c * w.2 + (Q y).2 = w.2 at h2
      change (Q y).2 = (1 - c) * w.2
      linarith
  have recover : ∀ (z : V) (a : ℝ), 0 < a → Q z = a • w → w ∈ Set.range Q := by
    intro z a ha hz
    have hm := quadratic_range_smul Q hscale (Set.mem_range_self z) (r := a⁻¹) (by positivity)
    rw [hz, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul] at hm
    exact hm
  by_cases hcpos : 0 < c
  · exact recover x c hcpos hx
  · exact recover y (1 - c) (by linarith) hy

theorem quadratic_range_convex (hzero : Q 0 = 0) (hcont : Continuous Q)
    (hscale : ∀ (r : ℝ) v, Q (r • v) = r ^ 2 • Q v)
    (hrot : ∀ (u v : V) (t : ℝ),
      Q (Real.cos t • u + Real.sin t • v) +
        Q (-Real.sin t • u + Real.cos t • v) = Q u + Q v) :
    Convex ℝ (Set.range Q) := by
  intro a ha b hb r s hr hs _
  obtain ⟨u, hu⟩ := quadratic_range_smul Q hscale ha hr
  obtain ⟨v, hv⟩ := quadratic_range_smul Q hscale hb hs
  rw [← hu, ← hv]
  exact quadratic_range_add Q hzero hcont hscale hrot u v

end
end QuadMatIneq.Stabilization.QMIFresh
end
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Set

theorem nonneg_of_all_mul_lower (z u : ℝ) (h : ∀ r : ℝ, 0 ≤ r → u ≤ r * z) : 0 ≤ z := by
  by_contra hz
  have hz' : 0 < -z := by linarith
  let r := (|u| + 1) / (-z)
  have hr : 0 < r := by dsimp [r]; positivity
  have he : r * (-z) = |u| + 1 := by
    dsimp [r]
    exact div_mul_cancel₀ _ (ne_of_gt hz')
  have hh := h r hr.le
  have hu := neg_abs_le u
  nlinarith

theorem cone_scalar_separator (C : Set (ℝ × ℝ)) (hC : Convex ℝ C) (h0 : 0 ∈ C)
    (hscale : ∀ z ∈ C, ∀ r : ℝ, 0 ≤ r → r • z ∈ C)
    (himp : ∀ z ∈ C, 0 ≤ z.1 → 0 ≤ z.2)
    (hslater : ∃ z ∈ C, 0 < z.1) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ z ∈ C, α * z.1 ≤ z.2 := by
  let B : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ z.2 < 0}
  have hBc : Convex ℝ B := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.1 + b * y.1 ∧ a * x.2 + b * y.2 < 0
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    constructor
    · by_cases hapos : 0 < a
      · exact add_pos_of_pos_of_nonneg (mul_pos hapos hx1) (mul_nonneg hb hy1.le)
      · have ha0 : a = 0 := by linarith
        have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy1
    · by_cases hapos : 0 < a
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hapos hx2) (mul_nonpos_of_nonneg_of_nonpos hb hy2.le)
      · have ha0 : a = 0 := by linarith
        have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy2
  have hBo : IsOpen B := (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_snd continuous_const)
  have hdis : Disjoint B C := by
    apply Set.disjoint_left.mpr
    intro z hz hc
    exact (himp z hc hz.1.le).not_gt hz.2
  obtain ⟨f, u, hB, hsep⟩ := geometric_hahn_banach_open hBc hBo hC hdis
  have hu : u ≤ 0 := by simpa using hsep 0 h0
  let a := f (1, 0)
  let b := f (0, 1)
  have hf : ∀ z : ℝ × ℝ, f z = a * z.1 + b * z.2 := by
    intro z
    have he : z = z.1 • (1, 0) + z.2 • (0, 1) := by ext <;> simp
    calc
      f z = f (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg f he
      _ = a * z.1 + b * z.2 := by
        rw [map_add, map_smul, map_smul]
        change z.1 * a + z.2 * b = a * z.1 + b * z.2
        ring
  have hneg : ∀ x y : ℝ, 0 < x → y < 0 → a * x + b * y < 0 := by
    intro x y hx hy
    have h := lt_of_lt_of_le (hB (x,y) ⟨hx,hy⟩) hu
    simpa only [hf, Prod.fst, Prod.snd] using h
  have ha : a ≤ 0 := by
    by_contra h
    have ha' : 0 < a := by linarith
    let x := (|b| + 1) / a
    have hx : 0 < x := by dsimp [x]; positivity
    have he : a * x = |b| + 1 := by dsimp [x]; field_simp
    have hn := hneg x (-1) hx (by norm_num)
    have hb := le_abs_self b
    nlinarith
  have hb : 0 ≤ b := by
    by_contra h
    have hb' : 0 < -b := by linarith
    let t := (|a| + 1) / (-b)
    have ht : 0 < t := by dsimp [t]; positivity
    have he : (-b) * t = |a| + 1 := by
      have hb0 : b ≠ 0 := by linarith
      dsimp [t]
      field_simp [hb0]
    have hn := hneg 1 (-t) (by norm_num) (by linarith)
    have ha' := neg_abs_le a
    nlinarith
  have hfC : ∀ z ∈ C, 0 ≤ f z := by
    intro z hz
    apply nonneg_of_all_mul_lower (f z) u
    intro r hr
    have hh := hsep (r • z) (hscale z hz r hr)
    simpa only [map_smul, smul_eq_mul] using hh
  have hbpos : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by linarith
    have hn := hneg 1 (-1) (by norm_num) (by norm_num)
    obtain ⟨z, hz, hzpos⟩ := hslater
    have hp := hfC z hz
    rw [hf, hb0, zero_mul, add_zero] at hp
    have ha' : a < 0 := by rw [hb0] at hn; linarith
    exact (mul_neg_of_neg_of_pos ha' hzpos).not_ge hp
  refine ⟨-a / b, div_nonneg (by linarith) hb, ?_⟩
  intro z hz
  have h := hfC z hz
  rw [hf] at h
  apply (mul_le_mul_iff_of_pos_left hbpos).mp
  have he : b * ((-a / b) * z.1) = -a * z.1 := by field_simp
  rw [he]
  nlinarith

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Matrix Set
variable {ι : Type*} [Fintype ι]

theorem qform_linear_combination (M : Matrix ι ι ℝ) (x y : ι → ℝ) (a b : ℝ) :
    qform M (a • x + b • y) = a ^ 2 * qform M x +
      a * b * (x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x)) + b ^ 2 * qform M y := by
  simp only [qform_add, qform_smul, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

theorem qform_rotation (M : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    qform M (Real.cos t • x + Real.sin t • y) +
      qform M (-Real.sin t • x + Real.cos t • y) = qform M x + qform M y := by
  rw [qform_linear_combination, qform_linear_combination]
  calc
    _ = (Real.cos t ^ 2 + Real.sin t ^ 2) * (qform M x + qform M y) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

def jointQuadratic (N M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ × ℝ :=
  (qform N x, qform M x)

theorem jointQuadratic_scale (N M : Matrix ι ι ℝ) (r : ℝ) (x : ι → ℝ) :
    jointQuadratic N M (r • x) = r ^ 2 • jointQuadratic N M x := by
  ext <;> simp [jointQuadratic, qform_smul]

theorem jointQuadratic_range_convex (N M : Matrix ι ι ℝ) :
    Convex ℝ (Set.range (jointQuadratic N M)) := by
  apply quadratic_range_convex (jointQuadratic N M)
  · simp [jointQuadratic]
  · exact (continuous_qform N).prodMk (continuous_qform M)
  · exact jointQuadratic_scale N M
  · intro x y t
    apply Prod.ext <;> exact qform_rotation _ x y t

theorem scalar_s_lemma (M N : Matrix ι ι ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hslater : ∃ x, 0 < qform N x)
    (himp : ∀ x, 0 ≤ qform N x → 0 ≤ qform M x) :
    ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef := by
  obtain ⟨α, hα, hbound⟩ := cone_scalar_separator (Set.range (jointQuadratic N M))
    (jointQuadratic_range_convex N M) (by exact ⟨0, by simp [jointQuadratic]⟩)
    (by
      intro z hz r hr
      exact quadratic_range_smul (jointQuadratic N M) (jointQuadratic_scale N M) hz hr)
    (by rintro z ⟨x, rfl⟩ hx; exact himp x hx)
    (by obtain ⟨x, hx⟩ := hslater; exact ⟨jointQuadratic N M x, ⟨x, rfl⟩, hx⟩)
  refine ⟨α, hα, posSemidef_of_qform (hM.sub (hN.smul (by rfl))) ?_⟩
  intro x
  have h := hbound (jointQuadratic N M x) (Set.mem_range_self x)
  change α * qform N x ≤ qform M x at h
  rw [qform_matrix_sub, qform_matrix_smul]
  linarith

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalar_strict_margin_certificate (M N : Matrix ι ι ℝ)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hfeas : ∃ x : ι → ℝ, x ≠ 0 ∧ 0 ≤ qform N x)
    (himp : ∀ x, x ≠ 0 → 0 ≤ qform N x → 0 < qform M x) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧ (M - α • N - β • (1 : Matrix ι ι ℝ)).PosSemidef := by
  obtain ⟨w, hw, hwN⟩ := hfeas
  obtain ⟨d, hd, hmargin⟩ := quadratic_strict_unit_margin M N himp ⟨w, hw⟩
  let ε := d / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hI : (1 : Matrix ι ι ℝ).IsHermitian := Matrix.isHermitian_one
  have hεI : (ε • (1 : Matrix ι ι ℝ)).IsHermitian := hI.smul (by rfl)
  have hslater : ∃ x, 0 < qform (N + ε • (1 : Matrix ι ι ℝ)) x := by
    refine ⟨w, ?_⟩
    rw [qform_matrix_add, qform_matrix_smul, qform_one]
    exact add_pos_of_nonneg_of_pos hwN (mul_pos hε (squareNorm_pos hw))
  have hpert : ∀ x, 0 ≤ qform (N + ε • (1 : Matrix ι ι ℝ)) x →
      0 ≤ qform (M - ε • (1 : Matrix ι ι ℝ)) x := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have he : 0 < squareNorm x := squareNorm_pos hx0
    let r := (Real.sqrt (squareNorm x))⁻¹
    have hr : 0 < r := by dsimp [r]; positivity
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hunit : squareNorm (r • x) = 1 := squareNorm_normalize hx0
    have hre : r ^ 2 * squareNorm x = 1 := by
      simpa only [squareNorm_smul] using hunit
    rw [qform_matrix_add, qform_matrix_smul, qform_one] at hx
    have hNnorm : -(d / 2) ≤ qform N (r • x) := by
      rw [qform_smul]
      have hmul := mul_nonneg hr2.le hx
      dsimp [ε] at hx hmul
      nlinarith
    have hMnorm := hmargin (r • x) hunit hNnorm
    rw [qform_smul] at hMnorm
    rw [qform_matrix_sub, qform_matrix_smul, qform_one]
    have hscaled : 0 ≤ r ^ 2 * (qform M x - ε * squareNorm x) := by
      dsimp [ε]
      nlinarith
    by_contra hneg
    have hh := mul_neg_of_pos_of_neg hr2 (lt_of_not_ge hneg)
    linarith
  obtain ⟨α, hα, hc⟩ := scalar_s_lemma (M - ε • (1 : Matrix ι ι ℝ))
    (N + ε • (1 : Matrix ι ι ℝ)) (hM.sub hεI) (hN.add hεI) hslater hpert
  refine ⟨α, ε, hα, hε, posSemidef_of_qform ((hM.sub (hN.smul (by rfl))).sub hεI) ?_⟩
  intro x
  have h := qform_nonneg hc x
  simp only [qform_matrix_sub, qform_matrix_add, qform_matrix_smul, qform_one] at h ⊢
  have hpos := mul_nonneg hα (mul_nonneg hε.le (squareNorm_nonneg x))
  nlinarith

theorem scalar_strict_s_lemma (M N : Matrix ι ι ℝ)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hfeas : ∃ x : ι → ℝ, x ≠ 0 ∧ 0 ≤ qform N x)
    (himp : ∀ x, x ≠ 0 → 0 ≤ qform N x → 0 < qform M x) :
    ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosDef := by
  obtain ⟨α, β, hα, hβ, hc⟩ := scalar_strict_margin_certificate M N hM hN hfeas himp
  refine ⟨α, hα, posDef_of_qform (hM.sub (hN.smul (by rfl))) ?_⟩
  intro x hx
  have h := qform_nonneg hc x
  rw [qform_matrix_sub, qform_matrix_smul, qform_one] at h
  have hp := mul_pos hβ (squareNorm_pos hx)
  linarith

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem strict_matrix_margin (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hMneg : (-M.toBlocks₂₂).PosSemidef) (hG : (-N.toBlocks₂₂).PosSemidef)
    (hker : ∀ v, N.toBlocks₂₂*ᵥv=0 → N.toBlocks₁₂*ᵥv=0)
    (Z₀ : Matrix κ ι ℝ) (hZ₀ : (qmiForm N Z₀).PosSemidef)
    (himp : ∀ Z, (qmiForm N Z).PosSemidef → (qmiForm M Z).PosDef)
    (hne : ∃ x : ι → ℝ, x ≠ 0) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧ (M-α•N-β•topMatrix).PosSemidef := by
  obtain ⟨K,hK,hKK,hGK,_hKG,_hfix,hKpos,_hnorm,hdetect⟩ := psd_kernel_projector _ hG
  have hAnn := kernel_annihilation M N hM hN hMneg hG hker Z₀ hZ₀ himp hne
  have hNK : ∀ y, N*ᵥSum.elim (0 : ι → ℝ) (K*ᵥy)=0 := by
    intro y
    have h : N.toBlocks₂₂*ᵥ(K*ᵥy)=0 := by
      have hh : (-N.toBlocks₂₂)*ᵥ(K*ᵥy)=0 := by rw [Matrix.mulVec_mulVec,hGK,Matrix.zero_mulVec]
      simpa only [Matrix.neg_mulVec,neg_eq_zero] using hh
    exact vertical_null N _ (hker _ h) h
  have hMK : ∀ y, M*ᵥSum.elim (0 : ι → ℝ) (K*ᵥy)=0 := by
    intro y
    have h : N.toBlocks₂₂*ᵥ(K*ᵥy)=0 := by
      have hh : (-N.toBlocks₂₂)*ᵥ(K*ᵥy)=0 := by rw [Matrix.mulVec_mulVec,hGK,Matrix.zero_mulVec]
      simpa only [Matrix.neg_mulVec,neg_eq_zero] using hh
    exact vertical_null M _ (hAnn _ h).2 (hAnn _ h).1
  have hKr : ∀ y, K*ᵥ(y-K*ᵥy)=0 := by
    intro y
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hKK,sub_self]
  let V := verticalMatrix (ι:=ι) K
  have hV : V.PosSemidef := vertical_posSemidef K hKpos
  have hstrict : ∀ w : ι ⊕ κ → ℝ, w≠0 → 0≤qform (N-V) w → 0<qform (M+V) w := by
    intro w hw hn
    let x := w∘Sum.inl
    let y := w∘Sum.inr
    have he : w=Sum.elim x y := by ext i; cases i <;> rfl
    have hn0 : 0≤qform N w := by
      have hv := qform_nonneg hV w
      rw [qform_matrix_sub] at hn
      linarith
    have hx : x≠0 := by
      intro hx0
      have hn' := hn
      rw [qform_matrix_sub,he,hx0,vertical_qform,qform_blocks_self] at hn'
      simp only [qform_zero,zero_dotProduct,Matrix.mulVec_zero,dotProduct_zero,
        zero_add,add_zero] at hn'
      have hg := qform_nonneg hG y
      have hk := qform_nonneg hKpos y
      have heG : qform (-N.toBlocks₂₂) y = -qform N.toBlocks₂₂ y := by
        simp only [qform,Matrix.neg_mulVec,dotProduct_neg]
      have hyG : qform (-N.toBlocks₂₂) y=0 := by linarith
      have hyK : qform K y=0 := by linarith
      have hy := hdetect y hyG ((qform_zero_iff hKpos y).1 hyK)
      apply hw
      rw [he,hx0,hy]
      ext i; cases i <;> rfl
    obtain ⟨Z,hZx,hZ⟩ := feasible_interpolation N hN hG hker Z₀ hZ₀ x y hx (he ▸ hn0)
    have hm := qform_pos (himp Z hZ) hx
    rw [qmi_qform,hZx,←he] at hm
    rw [qform_matrix_add]
    exact add_pos_of_pos_of_nonneg hm (qform_nonneg hV w)
  have hfeas : ∃ w : ι ⊕ κ → ℝ, w≠0 ∧ 0≤qform (N-V) w := by
    obtain ⟨x,hx⟩ := hne
    let y := Z₀*ᵥx
    refine ⟨Sum.elim x (y-K*ᵥy), ?_, ?_⟩
    · intro h
      apply hx
      exact congrArg (fun w : ι ⊕ κ → ℝ => w∘Sum.inl) h
    · have he : Sum.elim x (y-K*ᵥy)=Sum.elim x y-Sum.elim (0 : ι → ℝ) (K*ᵥy) := by
        ext i; cases i <;> simp
      rw [qform_matrix_sub,vertical_qform]
      have hk : qform K (y-K*ᵥy)=0 := (qform_zero_iff hKpos _).2 (hKr y)
      rw [hk,sub_zero,he,qform_sub_null N hN _ _ (hNK y)]
      simpa only [qmi_qform] using qform_nonneg hZ₀ x
  obtain ⟨α,β,hα,hβ,hcert⟩ := scalar_strict_margin_certificate (M+V) (N-V)
    (hM.add hV.isHermitian) (hN.sub hV.isHermitian) hfeas hstrict
  refine ⟨α,β,hα,hβ,posSemidef_of_qform
    ((hM.sub (hN.smul (by rfl))).sub (topMatrix_hermitian.smul (by rfl))) ?_⟩
  intro w
  let x := w∘Sum.inl
  let y := w∘Sum.inr
  have he : w=Sum.elim x y := by ext i; cases i <;> rfl
  let u : ι ⊕ κ → ℝ := Sum.elim x (y-K*ᵥy)
  have hu : u=w-Sum.elim (0 : ι → ℝ) (K*ᵥy) := by rw [he]; ext i; cases i <;> simp [u]
  have hMu : qform M u=qform M w := by rw [hu]; exact qform_sub_null M hM _ _ (hMK y)
  have hNu : qform N u=qform N w := by rw [hu]; exact qform_sub_null N hN _ _ (hNK y)
  have hVu : qform V u=0 := by
    rw [vertical_qform]
    exact (qform_zero_iff hKpos _).2 (hKr y)
  have hc := qform_nonneg hcert u
  simp only [qform_matrix_sub,qform_matrix_add,qform_matrix_smul,qform_one,hMu,hNu,hVu,
    add_zero,sub_zero] at hc
  have huNorm : squareNorm u=squareNorm x+squareNorm (y-K*ᵥy) := by simp [squareNorm,u,Fintype.sum_sum_type]
  rw [huNorm] at hc
  have hrest := mul_nonneg hβ.le (squareNorm_nonneg (y-K*ᵥy))
  rw [qform_matrix_sub,qform_matrix_sub,qform_matrix_smul,qform_matrix_smul,he,topMatrix_qform]
  rw [←he]
  linarith

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem definite_matrix_slemma (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hG : (-N.toBlocks₂₂).PosDef)
    (hker : ∀ v, N.toBlocks₂₂*ᵥv=0 → N.toBlocks₁₂*ᵥv=0)
    (Z₀ : Matrix κ ι ℝ) (hZ₀ : (qmiForm N Z₀).PosSemidef)
    (himp : ∀ Z, (qmiForm N Z).PosSemidef → (qmiForm M Z).PosDef)
    (hne : ∃ x : ι → ℝ, x ≠ 0) :
    ∃ α : ℝ, 0 ≤ α ∧ (M-α•N).PosDef := by
  apply scalar_strict_s_lemma M N hM hN
  · obtain ⟨x,hx⟩ := hne
    refine ⟨Sum.elim x (Z₀*ᵥx), ?_, ?_⟩
    · intro h
      apply hx
      exact congrArg (fun w : ι ⊕ κ → ℝ => w∘Sum.inl) h
    · simpa only [qmi_qform] using qform_nonneg hZ₀ x
  · intro w hw hn
    let x := w∘Sum.inl
    let y := w∘Sum.inr
    have he : w=Sum.elim x y := by ext i; cases i <;> rfl
    have hx : x≠0 := by
      intro hx0
      have hy : y≠0 := by
        intro hy0
        apply hw
        rw [he,hx0,hy0]
        ext i; cases i <;> rfl
      have hp := qform_pos hG hy
      rw [he,hx0,qform_blocks_self] at hn
      simp only [qform_zero,zero_dotProduct,Matrix.mulVec_zero,dotProduct_zero,
        zero_add,add_zero] at hn
      simp only [qform,Matrix.neg_mulVec,dotProduct_neg] at hp
      change 0≤qform N.toBlocks₂₂ y at hn
      change 0 < -qform N.toBlocks₂₂ y at hp
      linarith
    obtain ⟨Z,hZx,hZ⟩ := feasible_interpolation N hN hG.posSemidef hker Z₀ hZ₀
      x y hx (he ▸ hn)
    have hm := qform_pos (himp Z hZ) hx
    rwa [qmi_qform,hZx,←he] at hm

end QuadMatIneq.Stabilization.QMIFresh
end


section

open Matrix

namespace QuadMatIneq.Stabilization.QMIFresh

variable {n m T : ℕ}

theorem native_forward_margin
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : InPi Φ)
    (hgen : ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ B : Matrix (Fin n) (Fin m) ℝ,
      (A,B) ∈ Sigma Φ X Um) (hinfo : InformativeQS Φ X Um) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ L : Matrix (Fin m) (Fin n) ℝ,
      ∃ β : ℝ, P.PosDef ∧ 0<β ∧ (lmi55 Φ X Um P L β).PosSemidef := by
  obtain ⟨hN,hG,hker⟩ := native_N_geometry Φ X Um hΦ
  by_cases hn0 : n=0
  · subst n
    refine ⟨1,0,1,Matrix.PosDef.one,by norm_num,?_⟩
    have hc := zero_state_margin (Nmat Φ X Um) hN hG
    have h := (lmi55_iff_certificate Φ X Um 1 0 1 hΦ.1 Matrix.PosDef.one).mpr hc
    simpa using h
  · have hn : 0<n := Nat.pos_of_ne_zero hn0
    obtain ⟨K,P,hP,hall⟩ := hinfo
    obtain ⟨Z,hZ⟩ := native_N_feasible Φ X Um hgen
    have hM := Mmat_geometry P K hP
    have hne : ∃ x : Fin n → ℝ, x≠0 := by
      refine ⟨fun _ => 1,?_⟩
      intro h
      have hh := congrFun h ⟨0,hn⟩
      norm_num at hh
    obtain ⟨α,β,hα,hβ,hc⟩ := strict_matrix_margin (Mmat P K) (Nmat Φ X Um)
      hM.1 hN hM.2 hG hker Z hZ (native_all_Z_implication Φ X Um P K hall) hne
    have hαpos := margin_coefficient_pos P K (Nmat Φ X Um) α β hn hP hα hc
    have hp := hP.smul (inv_pos.mpr hαpos)
    refine ⟨α⁻¹•P,K*(α⁻¹•P),α⁻¹*β,hp,mul_pos (inv_pos.mpr hαpos) hβ,?_⟩
    apply (lmi55_iff_certificate Φ X Um _ K _ hΦ.1 hp).mpr
    exact scale_margin_certificate P K (Nmat Φ X Um) α β hαpos hc

theorem native_forward_strict
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : InPi Φ)
    (hgen : ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ B : Matrix (Fin n) (Fin m) ℝ,
      (A,B) ∈ Sigma Φ X Um) (hnoise : (-Φ.toBlocks₂₂).PosDef)
    (hrank : (Matrix.fromRows (Xminus X) Um).rank=n+m) (hinfo : InformativeQS Φ X Um) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ L : Matrix (Fin m) (Fin n) ℝ,
      P.PosDef ∧ (lmi56 Φ X Um P L).PosDef := by
  obtain ⟨hN,_hG,hker⟩ := native_N_geometry Φ X Um hΦ
  have hG := native_N_lower_posDef Φ X Um hnoise hrank
  by_cases hn0 : n=0
  · subst n
    refine ⟨1,0,Matrix.PosDef.one,?_⟩
    have hc := zero_state_strict (Nmat Φ X Um) hN hG
    have h := (lmi56_iff_certificate Φ X Um 1 0 hΦ.1 Matrix.PosDef.one).mpr hc
    simpa using h
  · have hn : 0<n := Nat.pos_of_ne_zero hn0
    obtain ⟨K,P,hP,hall⟩ := hinfo
    obtain ⟨Z,hZ⟩ := native_N_feasible Φ X Um hgen
    have hM := Mmat_geometry P K hP
    have hne : ∃ x : Fin n → ℝ, x≠0 := by
      refine ⟨fun _ => 1,?_⟩
      intro h
      have hh := congrFun h ⟨0,hn⟩
      norm_num at hh
    obtain ⟨α,hα,hc⟩ := definite_matrix_slemma (Mmat P K) (Nmat Φ X Um)
      hM.1 hN hG hker Z hZ (native_all_Z_implication Φ X Um P K hall) hne
    have hαpos := margin_coefficient_pos P K (Nmat Φ X Um) α 0 hn hP hα
      (by simpa using hc.posSemidef)
    have hp := hP.smul (inv_pos.mpr hαpos)
    refine ⟨α⁻¹•P,K*(α⁻¹•P),hp,?_⟩
    apply (lmi56_iff_certificate Φ X Um _ K hΦ.1 hp).mpr
    have h := hc.smul (inv_pos.mpr hαpos)
    have he : α⁻¹•(Mmat P K-α•Nmat Φ X Um)=Mmat (α⁻¹•P) K-Nmat Φ X Um := by
      rw [Mmat_smul,smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hαpos),one_smul]
    rwa [he] at h

end QuadMatIneq.Stabilization.QMIFresh
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Matrix Set
variable {ι : Type*} [Fintype ι]

theorem qform_normalize_identity (M : Matrix ι ι ℝ) {x : ι → ℝ} (hx : x ≠ 0) :
    qform M x = squareNorm x * qform M ((Real.sqrt (squareNorm x))⁻¹ • x) := by
  let r := (Real.sqrt (squareNorm x))⁻¹
  have hre : r ^ 2 * squareNorm x = 1 := by
    simpa only [squareNorm_smul] using squareNorm_normalize hx
  rw [qform_smul]
  change qform M x = squareNorm x * (r ^ 2 * qform M x)
  calc
    _ = (r ^ 2 * squareNorm x) * qform M x := by rw [hre, one_mul]
    _ = _ := by ring

theorem unit_lower_to_global (M : Matrix ι ι ℝ) (c : ℝ)
    (hc : ∀ x, squareNorm x = 1 → c ≤ qform M x) :
    ∀ x, c * squareNorm x ≤ qform M x := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have h := mul_le_mul_of_nonneg_left (hc _ (squareNorm_normalize hx)) (squareNorm_nonneg x)
  rw [← qform_normalize_identity M hx] at h
  simpa only [mul_comm] using h

theorem unit_upper_to_global (M : Matrix ι ι ℝ) (C : ℝ)
    (hC : ∀ x, squareNorm x = 1 → qform M x ≤ C) :
    ∀ x, qform M x ≤ C * squareNorm x := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have h := mul_le_mul_of_nonneg_left (hC _ (squareNorm_normalize hx)) (squareNorm_nonneg x)
  rw [← qform_normalize_identity M hx] at h
  simpa only [mul_comm] using h

theorem positive_quadratic_bounds {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x, c * squareNorm x ≤ qform P x) ∧
      (∀ x, qform P x ≤ C * squareNorm x) := by
  by_cases hne : ∃ x : ι → ℝ, x ≠ 0
  · obtain ⟨c, hc, hcl⟩ := quadratic_strict_unit_margin P (0 : Matrix ι ι ℝ)
      (fun x hx _ => qform_pos hP hx) hne
    have hnonempty : Set.Nonempty {x : ι → ℝ | squareNorm x = 1} := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨_, squareNorm_normalize hx⟩
    obtain ⟨z, hz, hmax⟩ := squareNorm_unit_compact.exists_isMaxOn hnonempty
      (continuous_qform P).continuousOn
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨c, qform P z + 1, hc, by linarith [qform_pos hP hz0], ?_, ?_⟩
    · apply unit_lower_to_global
      intro x hx
      apply hcl x hx
      simpa [qform] using (show -(c / 2) ≤ 0 by linarith)
    · apply unit_upper_to_global
      intro x hx
      have h : qform P x ≤ qform P z := hmax hx
      linarith
  · have hz : ∀ x : ι → ℝ, x = 0 := by simpa using hne
    refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩ <;> intro x <;> simp [hz x]

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

noncomputable section
namespace QuadMatIneq.Stabilization.QMIFresh
open Matrix Filter Topology
variable {ι : Type*} [Fintype ι]

theorem lyapunov_energy_contraction (P B : Matrix ι ι ℝ) (hP : P.PosDef)
    (hD : (P - B * P * Bᵀ).PosDef) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ x, qform P (Bᵀ *ᵥ x) ≤ r * qform P x := by
  obtain ⟨_, C, _, hC, _, hupper⟩ := positive_quadratic_bounds hP
  obtain ⟨δ, _, hδ, _, hlower, _⟩ := positive_quadratic_bounds hD
  let r := C / (C + δ)
  have hden : 0 < C + δ := by positivity
  refine ⟨r, (div_pos hC hden).le, (div_lt_one hden).2 (by linarith), ?_⟩
  intro x
  have he : qform (B * P * Bᵀ) x = qform P (Bᵀ *ᵥ x) := by
    simpa only [transpose_transpose] using qform_congr P Bᵀ x
  have hd := hlower x
  rw [qform_matrix_sub, he] at hd
  have hu := hupper x
  have h1 := mul_le_mul_of_nonneg_left hd hden.le
  have h2 := mul_le_mul_of_nonneg_left hu hδ.le
  have h3 := mul_nonneg (sq_nonneg δ) (squareNorm_nonneg x)
  calc
    qform P (Bᵀ *ᵥ x) ≤ (C * qform P x) / (C + δ) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    _ = r * qform P x := by dsimp [r]; ring

variable [DecidableEq ι]

theorem lyapunov_energy_iterate (P B : Matrix ι ι ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ x, qform P (Bᵀ *ᵥ x) ≤ r * qform P x) (x : ι → ℝ) (k : ℕ) :
    qform P ((Bᵀ) ^ k *ᵥ x) ≤ r ^ k * qform P x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, pow_succ']
      exact (hstep _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih hr)

theorem lyapunov_transpose_coordinate_tendsto (P B : Matrix ι ι ℝ) (hP : P.PosDef)
    (hD : (P - B * P * Bᵀ).PosDef) (x : ι → ℝ) (i : ι) :
    Tendsto (fun k : ℕ => ((Bᵀ)^k *ᵥ x) i) atTop (𝓝 0) := by
  obtain ⟨r, hr, hr1, hstep⟩ := lyapunov_energy_contraction P B hP hD
  obtain ⟨c, _, hc, _, hlower, _⟩ := positive_quadratic_bounds hP
  have hbound : ∀ k : ℕ, squareNorm ((Bᵀ)^k *ᵥ x) ≤ (r ^ k * qform P x) / c := by
    intro k
    apply (le_div_iff₀ hc).2
    simpa only [mul_comm] using (hlower _).trans (lyapunov_energy_iterate P B r hr hstep x k)
  have hlim : Tendsto (fun k : ℕ => (r ^ k * qform P x) / c) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const (qform P x)).div_const c
  have hE : Tendsto (fun k : ℕ => squareNorm ((Bᵀ)^k *ᵥ x)) atTop (𝓝 0) :=
    squeeze_zero (fun k => squareNorm_nonneg _) hbound hlim
  have hsquare : Tendsto (fun k : ℕ => (((Bᵀ)^k *ᵥ x) i)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sq_nonneg _) _ hE
    intro k
    exact Finset.single_le_sum (fun j _ => sq_nonneg (((Bᵀ)^k *ᵥ x) j)) (Finset.mem_univ i)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using h

theorem lyapunov_powers_tendsto (P B : Matrix ι ι ℝ) (hP : P.PosDef)
    (hD : (P - B * P * Bᵀ).PosDef) :
    Tendsto (fun k : ℕ => B ^ k) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have h := lyapunov_transpose_coordinate_tendsto P B hP hD (Pi.single i 1) j
  simp only [← transpose_pow, mulVec_single_one] at h
  change Tendsto (fun k : ℕ => (B ^ k) i j) atTop (𝓝 0) at h
  exact h

end QuadMatIneq.Stabilization.QMIFresh
end
end


section

open Matrix
namespace QuadMatIneq.Stabilization.QMIFresh
variable {n m T : ℕ}

theorem native_margin_stabilizes
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (hP : P.PosDef) (β : ℝ) (hβ : 0 < β)
    (hc : (Mmat P K-Nmat Φ X Um-β•topMatrix).PosSemidef) :
    StabilizesAll Φ X Um P K := by
  intro AB hAB
  have hN := (sigma_iff_native_qmi Φ X Um AB.1 AB.2).mp hAB
  let Z := Matrix.fromRows AB.1ᵀ AB.2ᵀ
  have hM : (qmiForm (Mmat P K) Z).PosDef := by
    apply posDef_of_qform
      (by
        simpa [qmiForm] using
          Matrix.isHermitian_conjTranspose_mul_mul (Matrix.fromRows 1 Z) (Mmat_geometry P K hP).1)
    intro x hx
    have hn := qform_nonneg hN x
    have hh := qform_nonneg hc (Sum.elim x (Z*ᵥx))
    rw [qform_matrix_sub, qform_matrix_sub, qform_matrix_smul, topMatrix_qform] at hh
    rw [qmi_qform] at hn ⊢
    change 0 ≤ qform (Nmat Φ X Um) (Sum.elim x (Z*ᵥx)) at hn
    have hp := mul_pos hβ (squareNorm_pos hx)
    linarith
  have hlyap : (P-(AB.1+AB.2*K)*P*(AB.1+AB.2*K)ᵀ).PosDef := by
    simpa only [Z, Mmat_qmi] using hM
  exact ⟨hlyap, lyapunov_powers_tendsto P (AB.1+AB.2*K) hP hlyap⟩

theorem native_definite_stabilizes
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (hP : P.PosDef) (hc : (Mmat P K-Nmat Φ X Um).PosDef) :
    StabilizesAll Φ X Um P K := by
  intro AB hAB
  have hN := (sigma_iff_native_qmi Φ X Um AB.1 AB.2).mp hAB
  let Z := Matrix.fromRows AB.1ᵀ AB.2ᵀ
  have hM : (qmiForm (Mmat P K) Z).PosDef := by
    apply posDef_of_qform
      (by
        simpa [qmiForm] using
          Matrix.isHermitian_conjTranspose_mul_mul (Matrix.fromRows 1 Z) (Mmat_geometry P K hP).1)
    intro x hx
    have hne : Sum.elim x (Z*ᵥx) ≠ 0 := by
      intro h
      exact hx (congrArg (fun v : Fin n ⊕ (Fin n ⊕ Fin m) → ℝ => v∘Sum.inl) h)
    have hn := qform_nonneg hN x
    have hh := qform_pos hc hne
    rw [qform_matrix_sub] at hh
    rw [qmi_qform] at hn ⊢
    change 0 ≤ qform (Nmat Φ X Um) (Sum.elim x (Z*ᵥx)) at hn
    linarith
  have hlyap : (P-(AB.1+AB.2*K)*P*(AB.1+AB.2*K)ᵀ).PosDef := by
    simpa only [Z, Mmat_qmi] using hM
  exact ⟨hlyap, lyapunov_powers_tendsto P (AB.1+AB.2*K) hP hlyap⟩

theorem native_lmi55_stabilizes
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : Φ.IsHermitian) (P : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ) (hP : P.PosDef) (hβ : 0 < β)
    (hL : (lmi55 Φ X Um P L β).PosSemidef) :
    StabilizesAll Φ X Um P (L*P⁻¹) := by
  let : Invertible P := hP.isUnit.invertible
  have he : (L*P⁻¹)*P=L := by rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  apply native_margin_stabilizes Φ X Um P (L*P⁻¹) hP β hβ
  apply (lmi55_iff_certificate Φ X Um P (L*P⁻¹) β hΦ hP).mp
  rwa [he]

theorem native_lmi56_stabilizes
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ)
    (X : Matrix (Fin n) (Fin (T+1)) ℝ) (Um : Matrix (Fin m) (Fin T) ℝ)
    (hΦ : Φ.IsHermitian) (P : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) (hP : P.PosDef)
    (hL : (lmi56 Φ X Um P L).PosDef) :
    StabilizesAll Φ X Um P (L*P⁻¹) := by
  let : Invertible P := hP.isUnit.invertible
  have he : (L*P⁻¹)*P=L := by rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  apply native_definite_stabilizes Φ X Um P (L*P⁻¹) hP
  apply (lmi56_iff_certificate Φ X Um P (L*P⁻¹) hΦ hP).mp
  rwa [he]

end QuadMatIneq.Stabilization.QMIFresh
end


section

namespace QuadMatIneq.Stabilization

/-- Theorem 5.1, pp. 18–19. `hgen` is "the data `(U₋, X)` are generated by (2.1) with noise
model (2.3)": the true system `(A_s, B_s)` lies in `Σ`. -/
theorem theorem_5_1 {n m T : ℕ}
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (hΦ : InPi Φ)
    (hgen : ∃ As : Matrix (Fin n) (Fin n) ℝ, ∃ Bs : Matrix (Fin n) (Fin m) ℝ,
      (As, Bs) ∈ Sigma Φ X Um) :
    -- (a)
    (InformativeQS Φ X Um ↔
      ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ L : Matrix (Fin m) (Fin n) ℝ, ∃ β : ℝ,
        P.PosDef ∧ 0 < β ∧ (lmi55 Φ X Um P L β).PosSemidef) ∧
    -- (b)
    ((-Φ.toBlocks₂₂).PosDef → (Matrix.fromRows (Xminus X) Um).rank = n + m →
      (InformativeQS Φ X Um ↔
        ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ L : Matrix (Fin m) (Fin n) ℝ,
          P.PosDef ∧ (lmi56 Φ X Um P L).PosDef)) ∧
    -- Moreover, for (5.5)
    (∀ (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ),
      P.PosDef → 0 < β → (lmi55 Φ X Um P L β).PosSemidef → StabilizesAll Φ X Um P (L * P⁻¹)) ∧
    -- Moreover, for (5.6)
    (∀ (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ),
      P.PosDef → (lmi56 Φ X Um P L).PosDef → StabilizesAll Φ X Um P (L * P⁻¹)) := by
  refine ⟨⟨QMIFresh.native_forward_margin Φ X Um hΦ hgen, ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨P,L,β,hP,hβ,hL⟩
    refine ⟨L*P⁻¹,P,hP,?_⟩
    intro AB hAB
    exact (QMIFresh.native_lmi55_stabilizes Φ X Um hΦ.1 P L β hP hβ hL AB hAB).1
  · intro hnoise hrank
    refine ⟨QMIFresh.native_forward_strict Φ X Um hΦ hgen hnoise hrank, ?_⟩
    rintro ⟨P,L,hP,hL⟩
    refine ⟨L*P⁻¹,P,hP,?_⟩
    intro AB hAB
    exact (QMIFresh.native_lmi56_stabilizes Φ X Um hΦ.1 P L hP hL AB hAB).1
  · exact QMIFresh.native_lmi55_stabilizes Φ X Um hΦ.1
  · exact QMIFresh.native_lmi56_stabilizes Φ X Um hΦ.1

end QuadMatIneq.Stabilization
end


theorem solution {n m T : ℕ}
    (Φ : Matrix (Fin n ⊕ Fin T) (Fin n ⊕ Fin T) ℝ) (X : Matrix (Fin n) (Fin (T + 1)) ℝ)
    (Um : Matrix (Fin m) (Fin T) ℝ) (hΦ : QuadMatIneq.Stabilization.InPi Φ)
    (hgen : ∃ As : Matrix (Fin n) (Fin n) ℝ, ∃ Bs : Matrix (Fin n) (Fin m) ℝ,
      (As, Bs) ∈ QuadMatIneq.Stabilization.Sigma Φ X Um) :
    -- (a)
    (QuadMatIneq.Stabilization.InformativeQS Φ X Um ↔
      ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ L : Matrix (Fin m) (Fin n) ℝ, ∃ β : ℝ,
        P.PosDef ∧ 0 < β ∧ (QuadMatIneq.Stabilization.lmi55 Φ X Um P L β).PosSemidef) ∧
    -- (b)
    ((-Φ.toBlocks₂₂).PosDef → (Matrix.fromRows (QuadMatIneq.Stabilization.Xminus X) Um).rank = n + m →
      (QuadMatIneq.Stabilization.InformativeQS Φ X Um ↔
        ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ L : Matrix (Fin m) (Fin n) ℝ,
          P.PosDef ∧ (QuadMatIneq.Stabilization.lmi56 Φ X Um P L).PosDef)) ∧
    -- Moreover, for (5.5)
    (∀ (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) (β : ℝ),
      P.PosDef → 0 < β → (QuadMatIneq.Stabilization.lmi55 Φ X Um P L β).PosSemidef → QuadMatIneq.Stabilization.StabilizesAll Φ X Um P (L * P⁻¹)) ∧
    -- Moreover, for (5.6)
    (∀ (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ),
      P.PosDef → (QuadMatIneq.Stabilization.lmi56 Φ X Um P L).PosDef → QuadMatIneq.Stabilization.StabilizesAll Φ X Um P (L * P⁻¹)) := by
  exact QuadMatIneq.Stabilization.theorem_5_1 Φ X Um hΦ hgen
