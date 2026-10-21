-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P02.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:50:34.336273+00:00
-- url     : https://prove2.me/submissions/4df2b623-f869-4780-ac1d-bf62dbbcfaed

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

lemma g58a_pk_mul {ι : Type*} [Fintype ι] (n : ℕ) (A B : Matrix ι ι ℂ) :
    piKron n A * piKron n B = piKron n (A * B) := by
  ext x y
  simp only [Matrix.mul_apply, piKron, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma g58a_pk_T {ι : Type*} (n : ℕ) (A : Matrix ι ι ℂ) : (piKron n A)ᵀ = piKron n Aᵀ := by
  ext x y; simp [piKron]

lemma g58a_pk_H {ι : Type*} (n : ℕ) (A : Matrix ι ι ℂ) : (piKron n A)ᴴ = piKron n Aᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, piKron, Matrix.of_apply]
  rw [show star (∏ i, A (y i) (x i)) = starRingEnd ℂ (∏ i, A (y i) (x i)) from rfl, map_prod]
  rfl

lemma g58a_pk_one {ι : Type*} [DecidableEq ι] (n : ℕ) : piKron n (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp only [piKron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g58a_pk_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) (V : Matrix ι ι ℂ)
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) :
    piKron n V * (piKron n V)ᴴ = 1 ∧ (piKron n V)ᴴ * piKron n V = 1 := by
  have h1 : V * Vᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hV; rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : Vᴴ * V = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hV; rwa [Matrix.star_eq_conjTranspose] at this
  rw [g58a_pk_H, g58a_pk_mul, g58a_pk_mul, h1, h2, g58a_pk_one]
  exact ⟨rfl, rfl⟩

lemma g58a_T_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : Uᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  have hT : Uᵀᴴ = Uᴴᵀ := by ext; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hT, ← Matrix.transpose_mul]
  have := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.star_eq_conjTranspose] at this
  rw [this, Matrix.transpose_one]

theorem solution {d p q : ℕ} (hd : 2 ≤ d)
    (Phi : Superop (Sites (Fin d) p) (Sites (Fin d) q)) (hPhi : IsChannel Phi) :
    UnitaryEquivariant Phi ↔
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        Commute (choi Phi)
          (Matrix.kronecker (piKron p (U : Matrix (Fin d) (Fin d) ℂ))
            (piKron q (fun i j => conj ((U : Matrix (Fin d) (Fin d) ℂ) i j)))) := by
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
  have hconj : ∀ U : Matrix (Fin d) (Fin d) ℂ,
      (fun i j => conj (U i j)) = (Uᵀ)ᴴ := by
    intro U; ext i j; simp [Matrix.conjTranspose_apply]
  constructor
  · intro h U
    rw [g58a_choi_comm, hconj, g58a_pk_T, ← g58a_pk_H]
    set V := (U : Matrix (Fin d) (Fin d) ℂ)ᵀ with hVdef
    have hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ := g58a_T_unitary _ U.2
    -- extend equivariance at V to all matrices
    have heq : ∀ ρ, L (piKron p V * ρ * (piKron p V)ᴴ) = piKron q V * L ρ * (piKron q V)ᴴ := by
      intro ρ
      let L1 := L.comp ((LinearMap.mulLeft ℂ (piKron p V)).comp (LinearMap.mulRight ℂ (piKron p V)ᴴ)) -
        (LinearMap.mulLeft ℂ (piKron q V)).comp ((LinearMap.mulRight ℂ (piKron q V)ᴴ).comp L)
      have := g58a_zero_of_density L1 (by
        intro ρ hρ
        simp only [L1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply, sub_eq_zero, hL]
        have := h ⟨V, hV⟩ ρ hρ
        simp only [conjSuperop, ← g58a_pk_H] at this
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]; exact this) ρ
      simp only [L1, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at this; exact this
    intro ρ
    obtain ⟨p1, p2⟩ := g58a_pk_unit p V hV
    obtain ⟨q1, q2⟩ := g58a_pk_unit q V hV
    have A : L (piKron p V * ρ) = piKron q V * L (ρ * piKron p V) * (piKron q V)ᴴ := by
      rw [← heq]
      congr 1
      rw [Matrix.mul_assoc, Matrix.mul_assoc, p1, Matrix.mul_one]
    rw [A, ← Matrix.mul_assoc, ← Matrix.mul_assoc, q2, Matrix.one_mul]
  · intro h W ρ hρ
    set V := (W : Matrix (Fin d) (Fin d) ℂ) with hVdef
    have hU : Vᵀ ∈ Matrix.unitaryGroup (Fin d) ℂ := g58a_T_unitary _ W.2
    have C := (g58a_choi_comm L _ _).mp (h ⟨Vᵀ, hU⟩)
    simp only [hconj, Matrix.transpose_transpose, g58a_pk_T] at C
    rw [← g58a_pk_H] at C
    obtain ⟨p1, p2⟩ := g58a_pk_unit p V W.2
    obtain ⟨q1, q2⟩ := g58a_pk_unit q V W.2
    have := C (ρ * (piKron p V)ᴴ)
    rw [Matrix.mul_assoc ρ, p2, Matrix.mul_one] at this
    show L (piKron p V * ρ * (piKron p V)ᴴ) = piKron q V * L ρ * (piKron q V)ᴴ
    calc L (piKron p V * ρ * (piKron p V)ᴴ)
        = piKron q V * ((piKron q V)ᴴ * L (piKron p V * (ρ * (piKron p V)ᴴ))) := by
          rw [← Matrix.mul_assoc, q1, Matrix.one_mul, Matrix.mul_assoc]
      _ = piKron q V * L ρ * (piKron q V)ᴴ := by rw [this, Matrix.mul_assoc]

end
