-- Prove2me | solution 1 for ReciprocityTheory.PGsh.a1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:01.450129+00:00
-- url     : https://prove2.me/submissions/2e9f40b3-298e-495c-895e-4ce41be7100f

import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.PGsh
open Matrix
private theorem smul_one_mulVec_dual_lattices {D n : Type*} [CommRing D] [Fintype n] [DecidableEq n] (c : D)
    (v : n → D) : (c • (1 : Matrix n n D)) *ᵥ v = c • v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
private lemma map_smul_one_mulVec {D K n : Type*} [CommRing D] [Field K] [Algebra D K]
    [Fintype n] [DecidableEq n] (c : D) (v : n → K) :
    ((c • (1 : Matrix n n D)).map (algebraMap D K)) *ᵥ v = c • v := by
  have h : ((c • (1 : Matrix n n D)).map (algebraMap D K)) = (algebraMap D K c) • (1 : Matrix n n K) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h, smul_one_mulVec_dual_lattices, algebraMap_smul]
private theorem exists_mulVec_eq_smul_of_mul_eq_smul_one {D p n : Type*} [CommRing D] [Fintype n] [Fintype p]
    [DecidableEq p] (H : Matrix p n D) (L : Matrix n p D) (c : D) (h : H * L = c • 1) (f : p → D) :
    ∃ t : n → D, H *ᵥ t = c • f :=
  ⟨L *ᵥ f, by rw [Matrix.mulVec_mulVec, h, smul_one_mulVec_dual_lattices]⟩
private theorem exists_integral_smul_of_mulVec_integral {D K p n : Type*} [CommRing D] [Field K] [Algebra D K]
    [Fintype n] [Fintype p] [DecidableEq p] (B : Matrix p n D) (W : Matrix n p D) (c : D)
    (h : B * W = c • 1) (x : p → K) (w : n → D)
    (hx : W.map (algebraMap D K) *ᵥ x = algebraMap D K ∘ w) :
    ∃ y : p → D, c • x = algebraMap D K ∘ y := by
  refine ⟨B *ᵥ w, ?_⟩
  rw [← map_smul_one_mulVec c x, ← h, Matrix.map_mul, ← Matrix.mulVec_mulVec, hx]
  funext i
  exact (RingHom.map_mulVec (algebraMap D K) B w i).symm
private theorem exists_mulVec_eq_of_mulVec_eq_zero {D K p n : Type*} [CommRing D] [Field K] [Algebra D K]
    [IsFractionRing D K] [Fintype n] [DecidableEq n] [Fintype p] (H B : Matrix p n D)
    (L W : Matrix n p D) (c : D) (hc : c ≠ 0) (h : L * H + W * B = c • 1) (t : n → K)
    (ht : H.map (algebraMap D K) *ᵥ t = 0) :
    ∃ x : p → K, W.map (algebraMap D K) *ᵥ x = t := by
  have hc' : algebraMap D K c ≠ 0 := by
    intro h0
    exact hc (IsFractionRing.injective D K (h0.trans (map_zero _).symm))
  have hmap : L.map (algebraMap D K) * H.map (algebraMap D K)
      + W.map (algebraMap D K) * B.map (algebraMap D K)
      = (c • (1 : Matrix n n D)).map (algebraMap D K) := by
    rw [← h, Matrix.map_add _ (fun a b => map_add (algebraMap D K) a b), Matrix.map_mul,
      Matrix.map_mul]
  have e1 : (L.map (algebraMap D K) * H.map (algebraMap D K)) *ᵥ t = 0 := by
    rw [← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero]
  have hWB : c • t = (W.map (algebraMap D K) * B.map (algebraMap D K)) *ᵥ t := by
    rw [← map_smul_one_mulVec c t, ← hmap, Matrix.add_mulVec, e1, zero_add]
  refine ⟨(algebraMap D K c)⁻¹ • (B.map (algebraMap D K) *ᵥ t), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hWB, ← algebraMap_smul K c t,
    inv_smul_smul₀ hc']
end ReciprocityTheory.PGsh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
namespace ReciprocityTheory.PGsh
theorem _root_.solution : ExistsPointLeviLogNormSqPos := by
  unfold ExistsPointLeviLogNormSqPos
  intro D _ _ g E Φ c hE hdiag hdet hc hΦ
  dsimp only
  have hEinv : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hdet
  have hF : (Eᵀ)⁻¹ = -E⁻¹ := by
    rw [hE]
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, hEinv])
  obtain ⟨N, hN⟩ : ∃ N, N = E⁻¹ * Φᵀ * stdJ D g := ⟨_, rfl⟩
  have hNΦ : N * Φ = c • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) := by
    rw [hN, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦ, Matrix.mul_smul, hEinv]
  have hdetΦ : Φ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hNΦ
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have hΦN : Φ * N = c • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) := by
    have h2 : (Φ * N - c • 1) * Φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hNΦ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h3 : Φ.det • (Φ * N - c • 1) = 0 := by
      rw [← Matrix.mul_one (Φ * N - c • 1), ← Matrix.mul_smul, ← Matrix.mul_adjugate Φ,
        ← Matrix.mul_assoc (Φ * N - c • 1) Φ (Matrix.adjugate Φ), h2, Matrix.zero_mul]
    have h4 : Φ * N - c • 1 = 0 := by
      ext i j
      have := congrFun (congrFun h3 i) j
      simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hdetΦ
    exact sub_eq_zero.mp h4
  have hJJ : stdJ D g * stdJ D g = -1 := by
    rw [stdJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hG : Φ * E⁻¹ * Φᵀ = -(c • stdJ D g) := by
    have h := congrArg (· * stdJ D g) hΦN
    simp only [hN, Matrix.mul_assoc, hJJ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg,
      Matrix.mul_one] at h
    rw [← h, neg_neg, Matrix.mul_assoc]
  have hsub : ∀ r s : Fin g → Fin g ⊕ Fin g,
      Φ.submatrix r id * E⁻¹ * (Φ.submatrix s id)ᵀ = (-(c • stdJ D g)).submatrix r s := by
    intro r s
    rw [← hG]
    ext a b
    rfl
  have hHH : Φ.submatrix Sum.inl id * E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ = 0 := by
    rw [hsub]; ext a b; simp [stdJ]
  have hBH : Φ.submatrix Sum.inr id * E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ
      = -(c • (1 : Matrix (Fin g) (Fin g) D)) := by
    rw [hsub]; ext a b; by_cases h : a = b <;> simp [stdJ, h]
  have hHB : Φ.submatrix Sum.inl id * E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ
      = c • (1 : Matrix (Fin g) (Fin g) D) := by
    rw [hsub]; ext a b; by_cases h : a = b <;> simp [stdJ, h]
  have hJΦ1 : ∀ a j, (stdJ D g * Φ) (Sum.inl a) j = -Φ (Sum.inr a) j := by
    intro a j; simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hJΦ2 : ∀ a j, (stdJ D g * Φ) (Sum.inr a) j = Φ (Sum.inl a) j := by
    intro a j; simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hform : (Φ.submatrix Sum.inr id)ᵀ * Φ.submatrix Sum.inl id
      - (Φ.submatrix Sum.inl id)ᵀ * Φ.submatrix Sum.inr id = c • E := by
    rw [← hΦ]
    ext i j
    rw [Matrix.mul_assoc Φᵀ, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [hJΦ1, hJΦ2]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      id_eq, mul_neg, Finset.sum_neg_distrib]
    ring
  have hkey : E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ * Φ.submatrix Sum.inl id
      + (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ) * Φ.submatrix Sum.inr id = c • 1 := by
    have h := congrArg (E⁻¹ * ·) hform
    simp only [Matrix.mul_sub, Matrix.mul_smul, hEinv] at h
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← sub_eq_add_neg]
    exact h
  have h2 : Φ.submatrix Sum.inl id * (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ) = 0 := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hHH, neg_zero]
  have h3 : Φ.submatrix Sum.inr id * (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ)
      = c • (1 : Matrix (Fin g) (Fin g) D) := by
    rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hBH, neg_neg]
  have hT : (-E⁻¹ * (Φ.submatrix Sum.inl id)ᵀ)ᵀ = Φ.submatrix Sum.inl id * E⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_neg,
      Matrix.transpose_nonsing_inv, hF, neg_neg]
  rw [hF]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_mulVec_eq_smul_of_mul_eq_smul_one _ (E⁻¹ * (Φ.submatrix Sum.inr id)ᵀ) c
      (by rw [← Matrix.mul_assoc]; exact hHB)
  · exact h2
  · exact h3
  · rw [hT, Matrix.mul_assoc (Φ.submatrix Sum.inl id) E⁻¹ E, hEinv, Matrix.mul_one]
    exact h2
  · intro t ht
    exact exists_mulVec_eq_of_mulVec_eq_zero _ _ _ _ c hc hkey t ht
  · rintro x ⟨w, hw⟩
    exact exists_integral_smul_of_mulVec_integral _ _ c h3 x w hw
end ReciprocityTheory.PGsh
