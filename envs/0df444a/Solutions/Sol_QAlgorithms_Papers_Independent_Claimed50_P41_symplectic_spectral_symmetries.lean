-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_spectral_symmetries
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:10:46.243915+00:00
-- url     : https://prove2.me/submissions/cd3002be-c6b8-4b3f-9cda-4380e56f6903

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P41

open scoped Matrix

open Polynomial in
theorem g68q_palin (n : ℕ) (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hT : T ∈ Matrix.symplecticGroup (Fin n) ℂ) :
    T.charpoly.reverse = T.charpoly := by
  have hdet : T.det = 1 := SymplecticGroup.det_eq_one hT
  have hinv : T⁻¹ = (-Matrix.J (Fin n) ℂ) * Tᵀ * Matrix.J (Fin n) ℂ := by
    rw [← SymplecticGroup.coe_inv' ⟨T, hT⟩, SymplecticGroup.coe_inv]
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one)
  have h1 : T⁻¹.charpoly = T.charpoly := by
    rw [hinv, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, Matrix.mul_neg,
      Matrix.J_squared, neg_neg, Matrix.mul_one, Matrix.charpoly_transpose]
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, ← h1, Matrix.charpoly, Matrix.charmatrix]
  have : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ[X]) - (X : ℂ[X]) • T.map C =
      -(T.map C * (Matrix.scalar (Fin n ⊕ Fin n) (X : ℂ[X]) - (C : ℂ →+* ℂ[X]).mapMatrix T⁻¹)) := by
    have e1 : T.map C * Matrix.scalar _ (X : ℂ[X]) = (X : ℂ[X]) • T.map C := by
      ext i j; rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    have e2 : T.map C * (C : ℂ →+* ℂ[X]).mapMatrix T⁻¹ = 1 := by
      rw [RingHom.mapMatrix_apply, ← Matrix.map_mul, hTT, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Matrix.mul_sub, e1, e2, neg_sub]
  rw [this, Matrix.det_neg, Matrix.det_mul]
  have e3 : (T.map C).det = 1 := by
    rw [show T.map C = (C : ℂ →+* ℂ[X]).mapMatrix T from rfl, ← RingHom.map_det, hdet, map_one]
  rw [e3, one_mul, Fintype.card_sum, Fintype.card_fin, Even.neg_one_pow ⟨n, rfl⟩, one_mul]

open Polynomial in
theorem g68q_rev_lin (a : ℂ) (ha : a ≠ 0) : (X - C a).reverse = C (-a) * (X - C a⁻¹) := by
  ext i
  rw [coeff_reverse, natDegree_X_sub_C]
  rcases i with _ | _ | i
  · rw [revAt_le (by norm_num)]; simp [mul_inv_cancel₀ ha]
  · rw [revAt_le (by norm_num)]; simp
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_C]

open Polynomial in
theorem g68q_rev_pow (f : ℂ[X]) (k : ℕ) : (f ^ k).reverse = f.reverse ^ k := by
  induction k with
  | zero => simp [reverse, reflect_one]
  | succ k ih => rw [pow_succ, reverse_mul_of_domain, ih, pow_succ]

open Polynomial in
theorem g68q_recip_le (p : ℂ[X]) (hp : p ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    rootMultiplicity a p ≤ rootMultiplicity a⁻¹ p.reverse := by
  rw [le_rootMultiplicity_iff (by rwa [Ne, reverse_eq_zero])]
  obtain ⟨q, hq⟩ := pow_rootMultiplicity_dvd p a
  have : p.reverse = (X - C a⁻¹) ^ rootMultiplicity a p * (C (-a) ^ rootMultiplicity a p * q.reverse) := by
    conv_lhs => rw [hq]
    rw [reverse_mul_of_domain, g68q_rev_pow, g68q_rev_lin a ha, mul_pow]; ring
  rw [this]; exact dvd_mul_right _ _

open Polynomial in
theorem g68q_parity (p : ℂ[X]) (hp : p ≠ 0) (hrev : p.reverse = p) (hdeg : Even p.natDegree) (a : ℂ)
    (ha : a = 1 ∨ a = -1) : Even (rootMultiplicity a p) := by
  have ha0 : a ≠ 0 := by rcases ha with rfl | rfl <;> norm_num
  have haa : a * a = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hainv : a⁻¹ = a := by rw [inv_eq_of_mul_eq_one_right haa]
  set k := rootMultiplicity a p
  set q := p /ₘ (X - C a) ^ k
  have hpq : (X - C a) ^ k * q = p := pow_mul_divByMonic_rootMultiplicity_eq p a
  have hqa : q.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hq0 : q ≠ 0 := by rintro h; rw [h] at hqa; simp at hqa
  have hrevq : (X - C a) ^ k * (C (-a) ^ k * q.reverse) = (X - C a) ^ k * q := by
    rw [hpq]
    conv_rhs => rw [← hrev, ← hpq]
    rw [reverse_mul_of_domain, g68q_rev_pow, g68q_rev_lin a ha0, mul_pow, hainv]; ring
  have hq2 : C (-a) ^ k * q.reverse = q :=
    mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero a)) hrevq
  -- evaluation of the reverse at a
  letI : Invertible a := ⟨a, haa, haa⟩
  have hev := eval₂_reverse_mul_pow (RingHom.id ℂ) a q
  have hinva : ⅟a = a := rfl
  rw [hinva, eval₂_id, eval₂_id] at hev
  have hev2 := congrArg (eval a) hq2
  rw [eval_mul, eval_pow, eval_C] at hev2
  have key : (-a) ^ k = a ^ q.natDegree := by
    have : (-a) ^ k * q.eval a = a ^ q.natDegree * q.eval a := by
      calc (-a) ^ k * q.eval a = (-a) ^ k * (q.reverse.eval a * a ^ q.natDegree) := by rw [hev]
        _ = a ^ q.natDegree * ((-a) ^ k * q.reverse.eval a) := by ring
        _ = a ^ q.natDegree * q.eval a := by rw [hev2]
    exact mul_right_cancel₀ hqa this
  have hdegq : p.natDegree = k + q.natDegree := by
    rw [← hpq, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hq0, natDegree_pow, natDegree_X_sub_C, mul_one]
  rcases ha with rfl | rfl
  · rw [one_pow] at key
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp key
  · rw [neg_neg, one_pow] at key
    have hq : Even q.natDegree := (neg_one_pow_eq_one_iff_even (by norm_num)).mp key.symm
    rw [hdegq] at hdeg
    exact (Nat.even_add.mp hdeg).mpr hq

theorem g68q_sigma (n : ℕ) : sigma n = -Matrix.J (Fin n) ℝ := by
  simp [sigma, Matrix.J, Matrix.fromBlocks_neg]

theorem g68q_pres_iff {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) :
    PreservesCanonicalForm S ↔ S ∈ Matrix.symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff, PreservesCanonicalForm, g68q_sigma]
  simp [Matrix.mul_neg, Matrix.neg_mul]

open Polynomial in
theorem g68q_recip (p : ℂ[X]) (hp : p ≠ 0) (hrev : p.reverse = p) (a : ℂ) (ha : a ≠ 0) :
    rootMultiplicity a p = rootMultiplicity a⁻¹ p := by
  apply le_antisymm
  · have := g68q_recip_le p hp a ha; rwa [hrev] at this
  · have := g68q_recip_le p hp a⁻¹ (inv_ne_zero ha); rwa [hrev, inv_inv] at this

theorem solution (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    let p := (complexify S).charpoly
    ¬ p.IsRoot 0 ∧
    (∀ z : ℂ, Polynomial.rootMultiplicity z p = Polynomial.rootMultiplicity (star z) p) ∧
    (∀ z : ℂ, z ≠ 0 → Polynomial.rootMultiplicity z p =
      Polynomial.rootMultiplicity ((star z)⁻¹) p) ∧
    Even (Polynomial.rootMultiplicity (1 : ℂ) p) ∧
    Even (Polynomial.rootMultiplicity (-1 : ℂ) p) := by
  intro p
  have hT : complexify S ∈ Matrix.symplecticGroup (Fin n) ℂ :=
    SymplecticGroup.map_mem ((g68q_pres_iff S).mp hS) Complex.ofRealHom
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hrev : p.reverse = p := g68q_palin n _ hT
  have hdet : (complexify S).det = 1 := SymplecticGroup.det_eq_one hT
  have hconj : p.map (starRingEnd ℂ) = p := by
    simp only [p]
    rw [← Matrix.charpoly_map]
    congr 1
    ext i j
    simp [complexify]
  have hc : ∀ z : ℂ, Polynomial.rootMultiplicity z p = Polynomial.rootMultiplicity (star z) p := by
    intro z
    have h1 := Polynomial.le_rootMultiplicity_map (p := p) (f := starRingEnd ℂ) (by rw [hconj]; exact hp0) z
    have h2 := Polynomial.le_rootMultiplicity_map (p := p) (f := starRingEnd ℂ) (by rw [hconj]; exact hp0) (starRingEnd ℂ z)
    rw [hconj] at h1 h2
    rw [Complex.conj_conj] at h2
    exact le_antisymm h1 h2
  have hdeg : Even p.natDegree := by
    simp only [p]
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_sum, Fintype.card_fin]
    exact ⟨n, rfl⟩
  refine ⟨?_, hc, ?_, g68q_parity p hp0 hrev hdeg 1 (Or.inl rfl), g68q_parity p hp0 hrev hdeg (-1) (Or.inr rfl)⟩
  · intro h
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero] at h
    have := Matrix.det_eq_sign_charpoly_coeff (complexify S)
    rw [hdet] at this
    simp only [p] at h
    rw [h, mul_zero] at this
    exact one_ne_zero this
  · intro z hz
    rw [hc z, g68q_recip p hp0 hrev (star z) (star_ne_zero.mpr hz)]
