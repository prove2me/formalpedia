-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.j2_hermiticity_positivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:13:20.621345+00:00
-- url     : https://prove2.me/submissions/d462042b-7676-4587-92f5-3e2ab244eb4d

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50HP

open QAlgorithms.Papers.Independent.Dependency50.P50

lemma j2_apply {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (p q : Fin n × Fin m) : j2 T p q = T (Matrix.single p.1 q.1 1) p.2 q.2 := rfl

lemma expand {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin m) :
    T A a b = ∑ i, ∑ j, A i j * T (Matrix.single i j 1) a b := by
  have hA : A = ∑ i : Fin n, ∑ j : Fin n, A i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp [Matrix.smul_single]
  conv_lhs => rw [hA]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma key {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (QAlgorithms.tensorVec x y) (QAlgorithms.act (j2 T) (QAlgorithms.tensorVec x y)) =
      star (y : Fin m → ℂ) ⬝ᵥ (T (Matrix.vecMulVec (star (x : Fin n → ℂ)) x) *ᵥ (y : Fin m → ℂ)) := by
  have hP : ∀ a b, T (Matrix.vecMulVec (star (x : Fin n → ℂ)) x) a b =
      ∑ i, ∑ j, (star (x i) * x j) * T (Matrix.single i j 1) a b := by
    intro a b; rw [expand T]; rfl
  simp only [PiLp.inner_apply, QAlgorithms.act, QAlgorithms.tensorVec, j2_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Pi.star_apply,
    RCLike.inner_apply, RCLike.star_def, map_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [hP, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def]
  ring


lemma posSemidef_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ v : ι → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ h
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have hz := h v.ofLp
  have hre : (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).im = 0 := (Complex.nonneg_iff.mp hz).2.symm
  have hin : inner ℂ (M.toEuclideanLin v) v = conj (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)) := by
    rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
      dotProduct_comm]
  rw [hin, Complex.conj_conj]
  apply Complex.ext <;> simp [hre]

lemma preserves_iff {n m : ℕ}
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    PreservesHermiticity T ↔ ∀ A : (Matrix (Fin n) (Fin n) ℂ), T (Aᴴ) = (T A)ᴴ := by
  constructor
  · intro h A
    set H : Matrix (Fin n) (Fin n) ℂ := (1/2 : ℂ) • (A + Aᴴ) with hH
    set K : Matrix (Fin n) (Fin n) ℂ := (-Complex.I/2 : ℂ) • (A - Aᴴ) with hK
    have hHh : H.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
      simp [add_comm]
    have hKh : K.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hA : A = H + Complex.I • K := by
      rw [hH, hK]; ext i j; simp [Complex.ext_iff]; constructor <;> ring
    have hAs : Aᴴ = H - Complex.I • K := by
      rw [hH, hK]; ext i j; simp [Complex.ext_iff]; constructor <;> ring
    have h1 := h H hHh
    have h2 := h K hKh
    unfold Matrix.IsHermitian at h1 h2
    clear_value H K
    rw [hAs, hA, map_sub, map_add, map_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, h1, h2]
    simp [sub_eq_add_neg]
  · intro h A hA
    unfold Matrix.IsHermitian at hA ⊢
    rw [← h, hA]

lemma preserves_iff_units {n m : ℕ}
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    PreservesHermiticity T ↔ ∀ i j : Fin n,
      T (Matrix.single j i 1) = (T (Matrix.single i j 1))ᴴ := by
  rw [preserves_iff T]
  refine ⟨fun h i j => by simpa [Matrix.conjTranspose_single] using h (Matrix.single i j 1),
    fun h => ?_⟩
  let E := Matrix.stdBasis ℂ (Fin n) (Fin n)
  let f₁ : Matrix (Fin n) (Fin n) ℂ →ₛₗ[starRingEnd ℂ] Matrix (Fin m) (Fin m) ℂ :=
    T.comp (Matrix.conjTransposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap
  let f₂ : Matrix (Fin n) (Fin n) ℂ →ₛₗ[starRingEnd ℂ] Matrix (Fin m) (Fin m) ℂ :=
    (Matrix.conjTransposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap.comp T
  have : f₁ = f₂ := E.ext fun p => by
    obtain ⟨i, j⟩ := p
    show T ((E (i, j))ᴴ) = (T (E (i, j)))ᴴ
    rw [Matrix.stdBasis_eq_single, Matrix.conjTranspose_single, star_one]
    exact h i j
  intro A
  exact LinearMap.congr_fun this A

lemma herm_iff {n m : ℕ}
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (j2 T).IsHermitian ↔ ∀ i j : Fin n,
      T (Matrix.single j i 1) = (T (Matrix.single i j 1))ᴴ := by
  constructor
  · intro h i j
    ext a b
    have := congrFun (congrFun h (j, a)) (i, b)
    simpa [Matrix.conjTranspose_apply, j2_apply] using this.symm
  · intro h
    ext p q
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    simp only [Matrix.conjTranspose_apply, j2_apply]
    rw [h j i]
    simp [Matrix.conjTranspose_apply]

lemma psd_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ,
      A = ∑ k, Matrix.vecMulVec (star (B k)) (B k) := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  refine ⟨CFC.sqrt A, ?_⟩
  conv_lhs => rw [hAB]
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.conjTranspose_apply]

end X6P50HP

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50HP in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (PreservesHermiticity T ↔ (j2 T).IsHermitian) ∧
      (Positive T ↔ ∀ (x : EuclideanSpace ℂ (Fin n)) (y : EuclideanSpace ℂ (Fin m)),
        0 ≤ inner ℂ (QAlgorithms.tensorVec x y)
          (QAlgorithms.act (j2 T) (QAlgorithms.tensorVec x y))) := by
  refine ⟨by rw [preserves_iff_units, herm_iff], ⟨fun hT x y => ?_, fun h A hA => ?_⟩⟩
  · rw [key]
    exact (hT _ (Matrix.posSemidef_vecMulVec_star_self _)).dotProduct_mulVec_nonneg _
  · obtain ⟨B, hBA⟩ := psd_decomp A hA
    refine posSemidef_of_forall _ fun v => ?_
    rw [hBA, map_sum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    have := h (WithLp.toLp 2 (B k)) (WithLp.toLp 2 v)
    rw [key] at this
    exact this
