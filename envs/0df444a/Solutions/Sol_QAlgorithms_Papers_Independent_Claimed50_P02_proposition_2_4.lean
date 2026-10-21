-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P02.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:44:05.170917+00:00
-- url     : https://prove2.me/submissions/3fb30b54-a8d1-40de-9593-10fb6f881dbd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

lemma g58a_zero_of_units {n m : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (h : ∀ a b, L (Matrix.single a b 1) = 0) (M : Matrix n n ℂ) :
    L M = 0 := by
  rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have : Matrix.single a b (M a b) = M a b • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, h, smul_zero]

lemma g58a_zero_of_density {n m : Type*} [Fintype n] [DecidableEq n]
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (h : ∀ ρ, IsDensityMatrix ρ → L ρ = 0) (M : Matrix n n ℂ) :
    L M = 0 := by
  have hpsd : ∀ A : Matrix n n ℂ, A.PosSemidef → L A = 0 := by
    intro A hA
    have ht := hA.trace_nonneg
    rw [Complex.nonneg_iff] at ht
    set r := A.trace.re
    have htr : A.trace = (r : ℂ) := Complex.ext rfl (by simp [← ht.2])
    by_cases hr : r = 0
    · have : A = 0 := hA.trace_eq_zero_iff.mp (by rw [htr, hr]; simp)
      rw [this, map_zero]
    · have hd : IsDensityMatrix (((r⁻¹ : ℝ) : ℂ) • A) := by
        refine ⟨hA.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr ht.1)), ?_⟩
        rw [Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr]
        simp
      have : A = (r : ℂ) • (((r⁻¹ : ℝ) : ℂ) • A) := by
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr]; simp
      rw [this, map_smul, h _ hd, smul_zero]
  have hvv : ∀ v : n → ℂ, L (Matrix.vecMulVec v (star v)) = 0 :=
    fun v => hpsd _ (Matrix.posSemidef_vecMulVec_self_star v)
  apply g58a_zero_of_units L _ M
  intro a b
  set u : n → ℂ := Pi.single a 1
  set w : n → ℂ := Pi.single b 1
  have key : (4 : ℂ) • Matrix.single a b (1 : ℂ) =
      Matrix.vecMulVec (u + w) (star (u + w)) - Matrix.vecMulVec (u - w) (star (u - w)) +
      Complex.I • Matrix.vecMulVec (u + Complex.I • w) (star (u + Complex.I • w)) -
      Complex.I • Matrix.vecMulVec (u - Complex.I • w) (star (u - Complex.I • w)) := by
    ext i j
    simp only [u, w, Matrix.smul_apply, Matrix.single_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.vecMulVec_apply, Pi.add_apply, Pi.sub_apply, Pi.star_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, star_add, star_sub, star_mul', Complex.star_def, Complex.conj_I]
    split_ifs <;> simp <;> (try (exfalso; tauto)) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)
  have h4 : L ((4 : ℂ) • Matrix.single a b (1 : ℂ)) = 0 := by
    rw [key, map_sub, map_add, map_sub, map_smul, map_smul, hvv, hvv, hvv, hvv]; simp
  rw [map_smul] at h4
  exact (smul_eq_zero.mp h4).resolve_left (by norm_num)

lemma g58a_choi_comm {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (L : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    Commute (choi (⇑L)) (Matrix.kronecker X Y) ↔ ∀ ρ, Y * L (Xᵀ * ρ) = L (ρ * Xᵀ) * Y := by
  have hu1 : ∀ a b : n, Xᵀ * Matrix.single a b (1 : ℂ) = ∑ a', X a a' • Matrix.single a' b (1 : ℂ) := by
    intro a b; ext i j
    by_cases hb : b = j <;> simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, hb]
  have hu2 : ∀ a b : n, Matrix.single a b (1 : ℂ) * Xᵀ = ∑ b', X b' b • Matrix.single a b' (1 : ℂ) := by
    intro a b; ext i j
    by_cases ha : a = i <;> simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ha]
  have e1 : ∀ (a b : n) (c e : m), (Matrix.kronecker X Y * choi (⇑L)) (a, c) (b, e) =
      (Y * L (Xᵀ * Matrix.single a b 1)) c e := by
    intro a b c e
    rw [hu1, map_sum]
    simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, choi, map_smul, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∀ (a b : n) (c e : m), (choi (⇑L) * Matrix.kronecker X Y) (a, c) (b, e) =
      (L (Matrix.single a b 1 * Xᵀ) * Y) c e := by
    intro a b c e
    rw [hu2, map_sum]
    simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, choi, map_smul, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  constructor
  · intro hc
    let L' : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ :=
      (LinearMap.mulLeft ℂ Y).comp (L.comp (LinearMap.mulLeft ℂ Xᵀ)) -
        (LinearMap.mulRight ℂ Y).comp (L.comp (LinearMap.mulRight ℂ Xᵀ))
    have hz := g58a_zero_of_units L' (by
      intro a b
      simp only [L', LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply]
      rw [sub_eq_zero]
      ext c e
      rw [← e1, ← e2, hc.eq])
    intro ρ
    have := hz ρ
    simp only [L', LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, sub_eq_zero] at this
    exact this
  · intro h
    show choi (⇑L) * Matrix.kronecker X Y = Matrix.kronecker X Y * choi (⇑L)
    ext ⟨a, c⟩ ⟨b, e⟩
    rw [e1, e2, h]

lemma g58a_tp_T {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    (QAlgorithms.Schur.tensorPermutation d n π)ᵀ = QAlgorithms.Schur.tensorPermutation d n π⁻¹ := by
  ext y x
  simp only [Matrix.transpose_apply, QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
  · rintro rfl; funext i; simp [Equiv.Perm.inv_def]

lemma g58a_tp_H {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    (QAlgorithms.Schur.tensorPermutation d n π)ᴴ = (QAlgorithms.Schur.tensorPermutation d n π)ᵀ := by
  ext y x
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, QAlgorithms.Schur.tensorPermutation,
    Matrix.of_apply]
  split_ifs <;> simp

lemma g58a_tp_mul {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.tensorPermutation d n π * QAlgorithms.Schur.tensorPermutation d n π⁻¹ = 1 := by
  ext y x
  rw [Matrix.mul_apply]
  simp only [QAlgorithms.Schur.tensorPermutation, Matrix.of_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [Finset.sum_ite_eq' Finset.univ (x ∘ π)]
  simp only [Finset.mem_univ, if_true]
  congr 1
  apply propext
  constructor
  · rintro rfl; funext i; simp
  · rintro rfl; funext i; simp

lemma g58a_tp_mul' {d n : ℕ} (π : Equiv.Perm (Fin n)) :
    QAlgorithms.Schur.tensorPermutation d n π⁻¹ * QAlgorithms.Schur.tensorPermutation d n π = 1 := by
  simpa using g58a_tp_mul (d := d) π⁻¹

lemma g58a_tp_one {d n : ℕ} : QAlgorithms.Schur.tensorPermutation d n 1 = 1 := by
  ext y x; rfl

theorem solution {d p q : ℕ} (hd : 2 ≤ d)
    (Phi : Superop (Sites (Fin d) p) (Sites (Fin d) q)) (hPhi : IsChannel Phi) :
    SymmetricChannel Phi ↔
      ∀ (pi : Equiv.Perm (Fin p)) (sigma : Equiv.Perm (Fin q)),
        Commute (choi Phi)
          (Matrix.kronecker ((QAlgorithms.Schur.tensorPermutation _ _) pi) ((QAlgorithms.Schur.tensorPermutation _ _) sigma)) := by
  obtain ⟨m, E, -, hE⟩ := hPhi
  let L : Matrix (Sites (Fin d) p) (Sites (Fin d) p) ℂ →ₗ[ℂ] Matrix (Sites (Fin d) q) (Sites (Fin d) q) ℂ :=
    { toFun := Phi
      map_add' := fun A B => by
        simp only [hE, krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := fun c A => by
        simp only [hE, krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply] }
  have hL : ∀ ρ, L ρ = Phi ρ := fun _ => rfl
  have hchoi : choi Phi = choi (⇑L) := rfl
  rw [hchoi]
  constructor
  · rintro ⟨h1, h2⟩ π σ
    have h1' : ∀ (π : Equiv.Perm (Fin p)) ρ, L ((QAlgorithms.Schur.tensorPermutation d p π) * ρ * ((QAlgorithms.Schur.tensorPermutation d p π))ᴴ) = L ρ := by
      intro π ρ
      let L1 := L.comp ((LinearMap.mulLeft ℂ ((QAlgorithms.Schur.tensorPermutation d p π))).comp (LinearMap.mulRight ℂ ((QAlgorithms.Schur.tensorPermutation d p π))ᴴ)) - L
      have := g58a_zero_of_density L1 (by
        intro ρ hρ
        simp only [L1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply, sub_eq_zero, hL]
        have := h1 π ρ hρ
        simp only [conjSuperop] at this
        rw [← Matrix.mul_assoc]; exact this) ρ
      simp only [L1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [← this, Matrix.mul_assoc]
    have h2' : ∀ (σ : Equiv.Perm (Fin q)) ρ, (QAlgorithms.Schur.tensorPermutation d q σ) * L ρ * ((QAlgorithms.Schur.tensorPermutation d q σ))ᴴ = L ρ := by
      intro σ ρ
      let L1 := (LinearMap.mulLeft ℂ ((QAlgorithms.Schur.tensorPermutation d q σ))).comp ((LinearMap.mulRight ℂ ((QAlgorithms.Schur.tensorPermutation d q σ))ᴴ).comp L) - L
      have := g58a_zero_of_density L1 (by
        intro ρ hρ
        simp only [L1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply, sub_eq_zero, hL]
        have := h2 σ ρ hρ
        simp only [conjSuperop] at this
        rw [← Matrix.mul_assoc]; exact this) ρ
      simp only [L1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [← Matrix.mul_assoc] at this; exact this
    rw [g58a_choi_comm]
    intro ρ
    have A : L (((QAlgorithms.Schur.tensorPermutation d p π))ᵀ * ρ) = L (ρ * ((QAlgorithms.Schur.tensorPermutation d p π))ᵀ) := by
      have := h1' π⁻¹ (ρ * (QAlgorithms.Schur.tensorPermutation d p π⁻¹))
      rw [g58a_tp_H, g58a_tp_T, inv_inv] at this
      rw [g58a_tp_T]
      rw [← this]
      simp only [Matrix.mul_assoc, g58a_tp_mul', Matrix.mul_one]
    have B : ∀ τ, (QAlgorithms.Schur.tensorPermutation d q σ) * L τ = L τ * (QAlgorithms.Schur.tensorPermutation d q σ) := by
      intro τ
      calc (QAlgorithms.Schur.tensorPermutation d q σ) * L τ = (QAlgorithms.Schur.tensorPermutation d q σ) * L τ * (((QAlgorithms.Schur.tensorPermutation d q σ))ᴴ * (QAlgorithms.Schur.tensorPermutation d q σ)) := by
            rw [g58a_tp_H, g58a_tp_T, g58a_tp_mul', Matrix.mul_one]
        _ = ((QAlgorithms.Schur.tensorPermutation d q σ) * L τ * ((QAlgorithms.Schur.tensorPermutation d q σ))ᴴ) * (QAlgorithms.Schur.tensorPermutation d q σ) := by simp only [Matrix.mul_assoc]
        _ = L τ * (QAlgorithms.Schur.tensorPermutation d q σ) := by rw [h2']
    rw [A, B]
  · intro h
    have C : ∀ (π : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin q)) ρ,
        (QAlgorithms.Schur.tensorPermutation d q σ) * L (((QAlgorithms.Schur.tensorPermutation d p π))ᵀ * ρ) = L (ρ * ((QAlgorithms.Schur.tensorPermutation d p π))ᵀ) * (QAlgorithms.Schur.tensorPermutation d q σ) :=
      fun π σ => (g58a_choi_comm L _ _).mp (h π σ)
    constructor
    · intro π ρ _
      show L ((QAlgorithms.Schur.tensorPermutation d p π) * ρ * ((QAlgorithms.Schur.tensorPermutation d p π))ᴴ) = L ρ
      have := C π⁻¹ 1 (ρ * ((QAlgorithms.Schur.tensorPermutation d p π))ᴴ)
      rw [g58a_tp_one, Matrix.one_mul, Matrix.mul_one, g58a_tp_T, inv_inv, g58a_tp_H, g58a_tp_T] at this
      rw [g58a_tp_H, g58a_tp_T, Matrix.mul_assoc, this, Matrix.mul_assoc, g58a_tp_mul', Matrix.mul_one]
    · intro σ ρ _
      show (QAlgorithms.Schur.tensorPermutation d q σ) * L ρ * ((QAlgorithms.Schur.tensorPermutation d q σ))ᴴ = L ρ
      have := C 1 σ ρ
      rw [g58a_tp_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
      rw [this, Matrix.mul_assoc, g58a_tp_H, g58a_tp_T, g58a_tp_mul, Matrix.mul_one]

end
