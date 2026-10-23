-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P03.affinityAndLocalUnitaryInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:26:36.432173+00:00
-- url     : https://prove2.me/submissions/d7d5c648-e125-4fd5-8407-3bc1d9313544

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P03

lemma x8_nuc_right {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (X : Matrix I J ℂ) (R : Matrix J J ℂ) (hR : R ∈ unitary (Matrix J J ℂ)) :
    nuclearNorm (X * R) = nuclearNorm X := by
  set u : unitary (Matrix J J ℂ) := ⟨star R, Unitary.star_mem hR⟩
  let φ := Unitary.conjStarAlgAut ℂ (Matrix J J ℂ) u
  have hφ : ∀ M, φ M = star R * M * R := by
    intro M; simp [φ, u, Unitary.conjStarAlgAut_apply]
  have hM : (X * R)ᴴ * (X * R) = φ (Xᴴ * X) := by
    rw [hφ, Matrix.conjTranspose_mul]; simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hcont : Continuous φ :=
    (φ.toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional
  have hsa : IsSelfAdjoint (Xᴴ * X) := by
    simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using
      (Matrix.isHermitian_conjTranspose_mul_self X)
  unfold nuclearNorm
  rw [hM, ← StarAlgHomClass.map_cfc φ Real.sqrt (Xᴴ * X) (hφ := hcont) (ha := hsa), hφ,
    Matrix.trace_mul_cycle, Unitary.mul_star_self_of_mem hR, one_mul]

lemma x8_nuc_left {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X : Matrix I J ℂ) (L : Matrix I I ℂ) (hL : L ∈ unitary (Matrix I I ℂ)) :
    nuclearNorm (L * X) = nuclearNorm X := by
  unfold nuclearNorm
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ,
    ← Matrix.star_eq_conjTranspose, Unitary.star_mul_self_of_mem hL, Matrix.one_mul]


section x8
set_option linter.unusedSectionVars false
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- the vectorized-conjugation matrix `conj U ⊗ U` -/
def x8K (U : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ := Matrix.kronecker (U.map star) U

lemma x8K_mem {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    x8K U ∈ unitary (Matrix (I × I) (I × I) ℂ) :=
  Matrix.kronecker_mem_unitary (Matrix.map_star_mem_unitaryGroup_iff.mpr hU) hU

omit [DecidableEq I] [DecidableEq J] in
lemma x8_realign (U : Matrix I I ℂ) (V : Matrix J J ℂ) (rho : Matrix (I × J) (I × J) ℂ) :
    realignment (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) =
      x8K U * realignment rho * (x8K V)ᵀ := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [realignment, x8K, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Fintype.sum_prod_type,
    Finset.sum_mul, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d1 _ => ?_
  conv_lhs => arg 2; ext c1; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d2 _ => Finset.sum_congr rfl fun c1 _ =>
    Finset.sum_congr rfl fun c2 _ => ?_
  ring

def x8e (I : Type*) [DecidableEq I] : I × I → ℂ := fun a => if a.1 = a.2 then 1 else 0

omit [DecidableEq I] in
lemma x8_vecTR (rho : Matrix (I × J) (I × J) ℂ) :
    columnVec (traceRight rho) = realignment rho *ᵥ x8e J := by
  classical
  ext ⟨a1, a2⟩
  simp only [columnVec, traceRight, Matrix.of_apply, Matrix.mulVec, dotProduct, realignment,
    x8e, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

omit [DecidableEq J] in
lemma x8_vecTL (rho : Matrix (I × J) (I × J) ℂ) :
    columnVec (traceLeft rho) = Matrix.vecMul (x8e I) (realignment rho) := by
  classical
  ext ⟨b1, b2⟩
  simp only [columnVec, traceLeft, Matrix.of_apply, Matrix.vecMul, dotProduct, realignment,
    x8e, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

omit [DecidableEq J] in
lemma x8_orth {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (s t : I) :
    ∑ h, star (U h s) * U h t = if s = t then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) s) t
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [Matrix.star_apply] using this

omit [DecidableEq J] in
lemma x8_Ke_right {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (x8K U)ᵀ *ᵥ x8e I = x8e I := by
  ext ⟨t1, t2⟩
  simp only [x8K, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.map_apply, x8e, Fintype.sum_prod_type, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact x8_orth hU t1 t2

omit [DecidableEq J] in
lemma x8_Ke_left {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.vecMul (x8e I) (x8K U) = x8e I := by
  ext ⟨t1, t2⟩
  simp only [x8K, Matrix.vecMul, dotProduct, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.map_apply, x8e, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact x8_orth hU t1 t2

lemma x8_conj_vecTR {U : Matrix I I ℂ} {V : Matrix J J ℂ} (hV : V ∈ Matrix.unitaryGroup J ℂ)
    (rho : Matrix (I × J) (I × J) ℂ) :
    columnVec (traceRight (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ)) =
      x8K U *ᵥ columnVec (traceRight rho) := by
  rw [x8_vecTR, x8_vecTR, x8_realign, ← Matrix.mulVec_mulVec, x8_Ke_right hV,
    Matrix.mulVec_mulVec]

lemma x8_conj_vecTL {U : Matrix I I ℂ} {V : Matrix J J ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (rho : Matrix (I × J) (I × J) ℂ) :
    columnVec (traceLeft (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ)) =
      Matrix.vecMul (columnVec (traceLeft rho)) (x8K V)ᵀ := by
  rw [x8_vecTL, x8_vecTL, x8_realign, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    x8_Ke_left hU]

lemma x8_blocks {M N : Type*} [Fintype M] [Fintype N] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) N ℂ) (C : Matrix M (Fin n) ℂ)
    (D : Matrix M N ℂ) (L : Matrix M M ℂ) (R : Matrix N N ℂ) :
    (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 L : Matrix (Fin m ⊕ M) (Fin m ⊕ M) ℂ) *
        Matrix.fromBlocks A B C D *
        (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 R : Matrix (Fin n ⊕ N) (Fin n ⊕ N) ℂ) =
      Matrix.fromBlocks A (B * R) (L * C) (L * D * R) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

lemma x8_enh_conj {m n r : ℕ} (z : Parameters m n r) {U : Matrix I I ℂ} {V : Matrix J J ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup J ℂ)
    (rho : Matrix (I × J) (I × J) ℂ) :
    enhanced z (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) =
      (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (x8K U) :
          Matrix (Fin m ⊕ (I × I)) (Fin m ⊕ (I × I)) ℂ) * enhanced z rho *
        (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 (x8K V)ᵀ :
          Matrix (Fin n ⊕ (J × J)) (Fin n ⊕ (J × J)) ℂ) := by
  refine Eq.trans ?_ (x8_blocks _ _ _ _ _ _).symm
  unfold enhanced
  congr 1
  · ext i b
    rw [x8_conj_vecTL hU]
    erw [Matrix.mul_apply]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
  · ext a j
    rw [x8_conj_vecTR hV]
    erw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  · exact x8_realign U V rho

lemma x8_blk_mem {M : Type*} [Fintype M] [DecidableEq M] {m : ℕ} {K : Matrix M M ℂ}
    (hK : K ∈ unitary (Matrix M M ℂ)) :
    Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 K ∈
      unitary (Matrix (Fin m ⊕ M) (Fin m ⊕ M) ℂ) := by
  rw [Unitary.mem_iff] at hK ⊢
  simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply] at hK ⊢
  simp [hK.1, hK.2, Matrix.fromBlocks_one]

lemma x8_lin_TL {K : ℕ} (c : Fin K → ℂ) (rho : Fin K → Matrix (I × J) (I × J) ℂ) (b : J × J) :
    columnVec (traceLeft (∑ k, c k • rho k)) b = ∑ k, c k * columnVec (traceLeft (rho k)) b := by
  simp only [columnVec, traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma x8_lin_TR {K : ℕ} (c : Fin K → ℂ) (rho : Fin K → Matrix (I × J) (I × J) ℂ) (a : I × I) :
    columnVec (traceRight (∑ k, c k • rho k)) a = ∑ k, c k * columnVec (traceRight (rho k)) a := by
  simp only [columnVec, traceRight, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma x8_affine {m n r : ℕ} (z : Parameters m n r) {K : ℕ} (p : Fin K → ℝ)
    (rho : Fin K → Matrix (I × J) (I × J) ℂ) (hp : (∑ k, p k) = 1) :
    enhanced z (∑ k, (p k : ℂ) • rho k) = ∑ k, (p k : ℂ) • enhanced z (rho k) := by
  have hpc : (∑ k, (p k : ℂ)) = 1 := by exact_mod_cast hp
  ext (i | a) (j | b)
  · simp only [enhanced, Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, ← Finset.sum_mul, hpc, one_mul]
  · simp only [enhanced, Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, x8_lin_TL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  · simp only [enhanced, Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, x8_lin_TR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  · simp only [enhanced, Matrix.sum_apply, Matrix.smul_apply, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, realignment]

end x8

theorem x8_main {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) :
    (∀ (K : ℕ) (p : Fin K → ℝ)
      (rho : Fin K → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      (∀ k, 0 ≤ p k) → (∑ k, p k) = 1 → (∀ k, IsDensityMatrix (rho k)) →
      enhanced z (∑ k, (p k : ℂ) • rho k) =
        ∑ k, (p k : ℂ) • enhanced z (rho k)) ∧
    (∀ (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      IsDensityMatrix rho → ∀ (U : Matrix.unitaryGroup (Fin dA) ℂ)
      (V : Matrix.unitaryGroup (Fin dB) ℂ),
      nuclearNorm (enhanced z
        (Matrix.kronecker (U : Matrix (Fin dA) (Fin dA) ℂ) (V : Matrix (Fin dB) (Fin dB) ℂ) *
          rho * (Matrix.kronecker (U : Matrix (Fin dA) (Fin dA) ℂ)
            (V : Matrix (Fin dB) (Fin dB) ℂ))ᴴ)) = nuclearNorm (enhanced z rho)) := by
  refine ⟨fun K p rho _ hp _ => x8_affine z p rho hp, fun rho _ U V => ?_⟩
  rw [x8_enh_conj z U.2 V.2, x8_nuc_right _ _ (x8_blk_mem ?_), x8_nuc_left _ _ (x8_blk_mem ?_)]
  · exact x8K_mem U.2
  · exact Matrix.transpose_mem_unitaryGroup_iff.mpr (x8K_mem V.2)

end QAlgorithms.Papers.Independent.Information100.P03

open QAlgorithms.Papers.Independent.Information100.P03 in
theorem solution {dA dB m n r : ℕ} [NeZero dA] [NeZero dB]
    (z : Parameters m n r) :
    (∀ (K : ℕ) (p : Fin K → ℝ)
      (rho : Fin K → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      (∀ k, 0 ≤ p k) → (∑ k, p k) = 1 → (∀ k, QAlgorithms.IsDensityMatrix (rho k)) →
      enhanced z (∑ k, (p k : ℂ) • rho k) =
        ∑ k, (p k : ℂ) • enhanced z (rho k)) ∧
    (∀ (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      QAlgorithms.IsDensityMatrix rho → ∀ (U : Matrix.unitaryGroup (Fin dA) ℂ)
      (V : Matrix.unitaryGroup (Fin dB) ℂ),
      nuclearNorm (enhanced z
        (Matrix.kronecker (U : Matrix (Fin dA) (Fin dA) ℂ) (V : Matrix (Fin dB) (Fin dB) ℂ) *
          rho * (Matrix.kronecker (U : Matrix (Fin dA) (Fin dA) ℂ)
            (V : Matrix (Fin dB) (Fin dB) ℂ))ᴴ)) = nuclearNorm (enhanced z rho)) :=
  x8_main z
