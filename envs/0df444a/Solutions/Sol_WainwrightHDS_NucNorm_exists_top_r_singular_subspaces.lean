-- Prove2me | solution 1 for WainwrightHDS.NucNorm.exists_top_r_singular_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T10:29:48.050201+00:00
-- url     : https://prove2.me/submissions/6283161f-b18a-43ef-8146-a2e10b47fab0

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_Mspace
import Definitions.Def_WainwrightHDS_NucNorm_Mbar
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp
import Definitions.Def_WainwrightHDS_NucNorm_projMat
import Definitions.Def_WainwrightHDS_NucNorm_projM
import Definitions.Def_WainwrightHDS_NucNorm_projMperp
import Definitions.Def_WainwrightHDS_NucNorm_projMbar
import Definitions.Def_WainwrightHDS_NucNorm_projMbarPerp

set_option linter.unusedVariables false

namespace WainwrightHDS.NucNorm

lemma toEuclideanLin_mul {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_mul _ _ _ A B

lemma toEuclideanLin_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    Matrix.toEuclideanLin A.transpose = (Matrix.toEuclideanLin A).adjoint := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma starProjection_toLinearMap_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : Submodule ℝ E) :
    ((U.starProjection : E →L[ℝ] E).toLinearMap).adjoint = (U.starProjection : E →L[ℝ] E).toLinearMap := by
  rw [ContinuousLinearMap.adjoint_toLinearMap]
  congr 1
  have h : star U.starProjection = U.starProjection := (isSelfAdjoint_starProjection U).star_eq
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

lemma toEuclideanLin_projMat {d : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix.toEuclideanLin (projMat U) = (U.starProjection : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).toLinearMap := by
  dsimp [projMat]
  exact Matrix.toEuclideanLin.apply_symm_apply _

lemma projMat_transpose {d : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    (projMat U).transpose = projMat U := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_transpose, toEuclideanLin_projMat]
  exact starProjection_toLinearMap_adjoint U

lemma traceInner_comm {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = traceInner B A := by
  dsimp [traceInner]
  simp_rw [mul_comm]

lemma traceInner_add_left {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (A + B) C = traceInner A C + traceInner B C := by
  unfold traceInner
  simp_rw [Matrix.add_apply, add_mul, ← Finset.sum_add_distrib]

lemma traceInner_add_right {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  rw [traceInner_comm, traceInner_add_left, traceInner_comm B, traceInner_comm C]

lemma traceInner_sub_left {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (A - B) C = traceInner A C - traceInner B C := by
  unfold traceInner
  simp_rw [Matrix.sub_apply, sub_mul, ← Finset.sum_sub_distrib]

lemma frobSq_eq_traceInner_self {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    frobSq A = traceInner A A := by
  dsimp [frobSq, traceInner]
  simp_rw [sq]

lemma frobSq_nonneg {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) :
    0 ≤ frobSq A := by
  dsimp [frobSq]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma traceInner_eq_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = (A.transpose * B).trace := by
  dsimp [traceInner, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma projMat_mul_of_range_le {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (B : Matrix (Fin d₁) (Fin d₂) ℝ) (hB : LinearMap.range (Matrix.toEuclideanLin B) ≤ U) :
    projMat U * B = B := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul, toEuclideanLin_projMat]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (hB (LinearMap.mem_range_self _ x))

lemma mul_projMat_of_range_transpose_le {d₁ d₂ : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (B : Matrix (Fin d₁) (Fin d₂) ℝ) (hB : LinearMap.range (Matrix.toEuclideanLin B.transpose) ≤ V) :
    B * projMat V = B := by
  have h : projMat V * B.transpose = B.transpose := projMat_mul_of_range_le V B.transpose hB
  have h_tr := congr_arg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, projMat_transpose] at h_tr
  exact h_tr

lemma projMbar_mem_Mbar {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projMbar U V Δ ∈ Mbar U V := by
  dsimp [Mbar, projMbar]
  intro B hB
  rcases hB with ⟨hB_V, hB_U⟩
  rw [traceInner_sub_left]
  dsimp [projMbarPerp]
  have h_proj_U : projMat Uᗮ * B = B := projMat_mul_of_range_le Uᗮ B hB_U
  have h_proj_V : B * projMat Vᗮ = B := mul_projMat_of_range_transpose_le Vᗮ B hB_V
  have h_inner_eq : traceInner (projMat Uᗮ * Δ * projMat Vᗮ) B = traceInner Δ B := by
    rw [traceInner_eq_trace, traceInner_eq_trace]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, projMat_transpose, projMat_transpose]
    rw [Matrix.mul_assoc]
    have h_comm := Matrix.trace_mul_comm (projMat Vᗮ) (Δ.transpose * projMat Uᗮ * B)
    rw [h_comm]
    have h_assoc : (Δ.transpose * projMat Uᗮ * B) * projMat Vᗮ = Δ.transpose * (projMat Uᗮ * B * projMat Vᗮ) := by
      simp only [Matrix.mul_assoc]
    rw [h_assoc, h_proj_U, h_proj_V]
  rw [h_inner_eq, sub_self]

lemma projMbarPerp_mem_MbarPerp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projMbarPerp U V Δ ∈ MbarPerp U V := by
  dsimp [MbarPerp, projMbarPerp]
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, projMat_transpose, projMat_transpose]
    rw [toEuclideanLin_mul, toEuclideanLin_projMat]
    refine le_trans (LinearMap.range_comp_le_range _ _) ?_
    exact (Submodule.range_starProjection Vᗮ).le
  · rw [Matrix.mul_assoc, toEuclideanLin_mul, toEuclideanLin_projMat]
    refine le_trans (LinearMap.range_comp_le_range _ _) ?_
    exact (Submodule.range_starProjection Uᗮ).le

lemma frobSq_projMbar_le {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    frobSq (projMbar U V Δ) ≤ frobSq Δ := by
  have h_dec : Δ = projMbar U V Δ + projMbarPerp U V Δ := by
    dsimp [projMbar]
    abel
  have h_inner_zero : traceInner (projMbar U V Δ) (projMbarPerp U V Δ) = 0 :=
    projMbar_mem_Mbar U V Δ (projMbarPerp U V Δ) (projMbarPerp_mem_MbarPerp U V Δ)
  have h_exp : frobSq Δ = frobSq (projMbar U V Δ) + frobSq (projMbarPerp U V Δ) := by
    conv_lhs => rw [h_dec]
    rw [frobSq_eq_traceInner_self]
    rw [traceInner_add_left, traceInner_add_right, traceInner_add_right]
    rw [traceInner_comm (projMbarPerp U V Δ) (projMbar U V Δ)]
    rw [h_inner_zero]
    rw [← frobSq_eq_traceInner_self, ← frobSq_eq_traceInner_self]
    ring
  linarith [frobSq_nonneg (projMbarPerp U V Δ)]

lemma finrank_range_toEuclideanLin_le_min {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) ≤ min d₁ d₂ := by
  have h1 : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) ≤ d₁ := by
    have h := Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin M))
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h
    exact h
  have h2 : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin M)) ≤ d₂ := by
    have h := LinearMap.finrank_range_le (Matrix.toEuclideanLin M)
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h
    exact h
  exact le_min h1 h2

lemma singularValues_eq_zero_of_min_le {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : ℕ)
    (hi : min d₁ d₂ ≤ i) :
    (Matrix.toEuclideanLin M).singularValues i = 0 := by
  have h_le := (finrank_range_toEuclideanLin_le_min M).trans hi
  exact (Matrix.toEuclideanLin M).singularValues_eq_zero_iff_le_finrank_range.mpr h_le

lemma sum_singularValues_eq_nucNorm {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ∑ i : Fin d₂, (Matrix.toEuclideanLin M).singularValues i = nucNorm M := by
  dsimp [nucNorm, singVal]
  rw [Fin.sum_univ_eq_sum_range]
  have h_min_le : min d₁ d₂ ≤ d₂ := min_le_right d₁ d₂
  rw [← Finset.sum_range_add_sum_Ico _ h_min_le]
  have h_zero : ∑ i ∈ Finset.Ico (min d₁ d₂) d₂, (Matrix.toEuclideanLin M).singularValues i = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_Ico] at hx
    exact singularValues_eq_zero_of_min_le M x hx.1
  rw [h_zero, add_zero]

lemma norm_toEuclideanLin_apply_eigenvectorBasis {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ)
    (i : Fin d₂) :
    ‖Matrix.toEuclideanLin M (((Matrix.toEuclideanLin M).isSymmetric_adjoint_comp_self).eigenvectorBasis
      (by simp [finrank_euclideanSpace] : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂) i)‖ =
      (Matrix.toEuclideanLin M).singularValues i := by
  set T := Matrix.toEuclideanLin M
  set S := T.adjoint ∘ₗ T
  set hS := T.isSymmetric_adjoint_comp_self
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set v := hS.eigenvectorBasis hn i
  have h_inner_sq : ‖T v‖ ^ 2 = @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (T v) (T v) := by
    rw [real_inner_self_eq_norm_mul_norm, ← sq]
  have h_adj : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (T v) (T v) =
      @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ v (S v) := by
    rw [real_inner_comm (T v) (T v)]
    exact (LinearMap.adjoint_inner_right T v (T v)).symm
  have h_eig : S v = (hS.eigenvalues hn i) • v := by
    exact hS.apply_eigenvectorBasis hn i
  have h_inner_v : @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ v (S v) = hS.eigenvalues hn i := by
    rw [h_eig, inner_smul_right, real_inner_self_eq_norm_mul_norm, (hS.eigenvectorBasis hn).orthonormal.1 i, mul_one, mul_one]
  have h_sq_sing : T.singularValues i ^ 2 = hS.eigenvalues hn i := by
    exact T.sq_singularValues_fin hn i
  have h_norm_sq : ‖T v‖ ^ 2 = T.singularValues i ^ 2 := by
    rw [h_inner_sq, h_adj, h_inner_v, ← h_sq_sing]
  have h1 : 0 ≤ ‖T v‖ := norm_nonneg _
  have h2 : 0 ≤ T.singularValues i := T.singularValues_nonneg i
  have h_sqrt := congr_arg Real.sqrt h_norm_sq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at h_sqrt

theorem sum_inner_eq_trace {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (S U : E₂ →ₗ[ℝ] E₁) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E₂) :
    ∑ i, @inner ℝ E₁ _ (S (b i)) (U (b i)) = LinearMap.trace ℝ E₂ (S.adjoint.comp U) := by
  rw [LinearMap.trace_eq_sum_inner (S.adjoint.comp U) b]
  congr 1; ext i
  exact (LinearMap.adjoint_inner_right S (b i) (U (b i))).symm

noncomputable def makeU {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) : E₂ →ₗ[ℝ] E₁ :=
  ∑ j : ι, LinearMap.smulRight (innerSL ℝ (b j)).toLinearMap (u j)

theorem makeU_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) (x : E₂) :
    makeU b u x = ∑ j : ι, @inner ℝ E₂ _ (b j) x • u j := by
  simp [makeU]

theorem makeU_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) (i : ι) :
    makeU b u (b i) = u i := by
  rw [makeU_apply]
  have h_inner : ∀ j, @inner ℝ E₂ _ (b j) (b i) = if j = i then (1 : ℝ) else 0 := by
    intro j
    split_ifs with h
    · rw [h, real_inner_self_eq_norm_mul_norm, b.orthonormal.1 i, mul_one]
    · exact b.orthonormal.2 h
  simp_rw [h_inner]
  have h_term : ∀ j, (if j = i then (1 : ℝ) else 0) • u j = if j = i then u i else 0 := by
    intro j
    split_ifs with h
    · rw [h, one_smul]
    · rw [zero_smul]
  simp_rw [h_term]
  rw [Finset.sum_ite_eq']
  simp

lemma inner_sum_smul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ι → ℝ) (u : ι → E)
    (h_ortho : ∀ i j, i ≠ j → @inner ℝ E _ (u i) (u j) = 0) :
    @inner ℝ E _ (∑ i, c i • u i) (∑ j, c j • u j) = ∑ i, (c i) ^ 2 * ‖u i‖ ^ 2 := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  have h_inner_j : ∀ j, @inner ℝ E _ (c i • u i) (c j • u j) =
      c i * c j * @inner ℝ E _ (u i) (u j) := by
    intro j
    rw [inner_smul_left, inner_smul_right, conj_trivial, mul_assoc]
  simp_rw [h_inner_j]
  have h_single : ∑ j, c i * c j * @inner ℝ E _ (u i) (u j) = (c i) ^ 2 * ‖u i‖ ^ 2 := by
    rw [Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_mul_norm]
      ring
    · intro j _ hj
      rw [h_ortho i j hj.symm, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  exact h_single

theorem norm_makeU_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁)
    (h_ortho : ∀ i j, i ≠ j → @inner ℝ E₁ _ (u i) (u j) = 0)
    (h_norm : ∀ i, ‖u i‖ ≤ 1) (x : E₂) :
    ‖makeU b u x‖ ≤ ‖x‖ := by
  have h_inner_sq : ‖makeU b u x‖ ^ 2 = @inner ℝ E₁ _ (makeU b u x) (makeU b u x) := by
    rw [real_inner_self_eq_norm_mul_norm, ← sq]
  have h_makeU_inner : @inner ℝ E₁ _ (makeU b u x) (makeU b u x) =
      ∑ j : ι, (@inner ℝ E₂ _ (b j) x) ^ 2 * ‖u j‖ ^ 2 := by
    rw [makeU_apply]
    exact inner_sum_smul_self (fun j => @inner ℝ E₂ _ (b j) x) u h_ortho
  have h_term_le : ∀ j : ι, (@inner ℝ E₂ _ (b j) x) ^ 2 * ‖u j‖ ^ 2 ≤ (@inner ℝ E₂ _ (b j) x) ^ 2 := by
    intro j
    have hu_sq : ‖u j‖ ^ 2 ≤ 1 := by
      have : 0 ≤ ‖u j‖ := norm_nonneg _
      nlinarith [h_norm j]
    have : 0 ≤ (@inner ℝ E₂ _ (b j) x) ^ 2 := sq_nonneg _
    nlinarith
  have h_sum_le : (∑ j : ι, (@inner ℝ E₂ _ (b j) x) ^ 2 * ‖u j‖ ^ 2) ≤
      ∑ j : ι, (@inner ℝ E₂ _ (b j) x) ^ 2 :=
    Finset.sum_le_sum fun j _ => h_term_le j
  have h_parseval : (∑ j : ι, (@inner ℝ E₂ _ (b j) x) ^ 2) = ‖x‖ ^ 2 := by
    have h_parse := b.sum_inner_mul_inner x x
    have h_comm : ∀ j : ι, @inner ℝ E₂ _ x (b j) * @inner ℝ E₂ _ (b j) x = (@inner ℝ E₂ _ (b j) x) ^ 2 := by
      intro j
      rw [real_inner_comm x (b j), ← sq]
    simp_rw [h_comm] at h_parse
    rw [real_inner_self_eq_norm_mul_norm, ← sq] at h_parse
    exact h_parse
  have h_sq_le : ‖makeU b u x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h_inner_sq, h_makeU_inner]
    exact h_sum_le.trans (le_of_eq h_parseval)
  have h1 : 0 ≤ ‖makeU b u x‖ := norm_nonneg _
  have h2 : 0 ≤ ‖x‖ := norm_nonneg _
  have h_sqrt := Real.sqrt_le_sqrt h_sq_le
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at h_sqrt

noncomputable def polarVec {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin d₂) :
    EuclideanSpace ℝ (Fin d₁) :=
  let TM := Matrix.toEuclideanLin M
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  let b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  if ‖TM (b i)‖ = 0 then 0 else (‖TM (b i)‖)⁻¹ • TM (b i)

lemma polarVec_ortho {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i j : Fin d₂) (hij : i ≠ j) :
    @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (polarVec M i) (polarVec M j) = 0 := by
  dsimp [polarVec]
  set TM := Matrix.toEuclideanLin M
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set hS := TM.isSymmetric_adjoint_comp_self
  set b := hS.eigenvectorBasis hn
  split_ifs with hi hj
  · exact inner_zero_left _
  · exact inner_zero_left _
  · exact inner_zero_right _
  · rw [inner_smul_left, inner_smul_right, conj_trivial]
    have h_adj : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TM (b j)) =
        @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ (b i) ((TM.adjoint ∘ₗ TM) (b j)) := by
      exact (LinearMap.adjoint_inner_right TM (b i) (TM (b j))).symm
    have h_eig : (TM.adjoint ∘ₗ TM) (b j) = (hS.eigenvalues hn j) • b j :=
      hS.apply_eigenvectorBasis hn j
    rw [h_adj, h_eig, inner_smul_right]
    have hb_ortho : @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ (b i) (b j) = 0 :=
      b.orthonormal.2 hij
    rw [hb_ortho, mul_zero, mul_zero, mul_zero]

lemma polarVec_norm_le {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin d₂) :
    ‖polarVec M i‖ ≤ 1 := by
  dsimp [polarVec]
  set TM := Matrix.toEuclideanLin M
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  split_ifs with hi
  · rw [norm_zero]; exact zero_le_one
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hi]

lemma polarVec_inner_eval {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin d₂) :
    let TM := Matrix.toEuclideanLin M
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
    let b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
    @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (polarVec M i) = TM.singularValues i := by
  dsimp [polarVec]
  set TM := Matrix.toEuclideanLin M
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  have h_sv := norm_toEuclideanLin_apply_eigenvectorBasis M i
  split_ifs with hi
  · have hTM_zero : TM (b i) = 0 := norm_eq_zero.mp hi
    rw [hTM_zero, inner_zero_left, ← h_sv, hi]
  · rw [inner_smul_right]
    have h_sq : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TM (b i)) = ‖TM (b i)‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
    rw [h_sq, sq, ← mul_assoc, inv_mul_cancel₀ hi, one_mul, h_sv]

noncomputable def polarU {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    EuclideanSpace ℝ (Fin d₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁) :=
  let TM := Matrix.toEuclideanLin M
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  let b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  makeU b (polarVec M)

lemma norm_polarU_le {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (x : EuclideanSpace ℝ (Fin d₂)) :
    ‖polarU M x‖ ≤ ‖x‖ := by
  dsimp [polarU]
  exact norm_makeU_le _ (polarVec M) (polarVec_ortho M) (polarVec_norm_le M) x

lemma polarU_basis {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin d₂) :
    let TM := Matrix.toEuclideanLin M
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
    let b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
    polarU M (b i) = polarVec M i := by
  dsimp [polarU]
  exact makeU_basis _ (polarVec M) i

theorem trace_adjoint_comp_polarU_eq_nucNorm {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin M).adjoint.comp (polarU M)) =
      nucNorm M := by
  set TM := Matrix.toEuclideanLin M
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  rw [← sum_inner_eq_trace TM (polarU M) b]
  have h_term : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (polarU M (b i)) =
      TM.singularValues i := by
    intro i
    rw [polarU_basis M i]
    exact polarVec_inner_eval M i
  simp_rw [h_term]
  exact sum_singularValues_eq_nucNorm M

lemma toEuclideanLin_projMperp {d₁ d₂ : ℕ} (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (h_UT : ∀ x ∈ V, (U.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)) (Matrix.toEuclideanLin Θstar x) =
      Matrix.toEuclideanLin Θstar x) :
    Matrix.toEuclideanLin (projMperp U V Θstar) =
      (Matrix.toEuclideanLin Θstar).comp
        (LinearMap.id - (V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap) := by
  dsimp [projMperp, projM]
  rw [map_sub, Matrix.mul_assoc, toEuclideanLin_mul, toEuclideanLin_mul]
  rw [toEuclideanLin_projMat, toEuclideanLin_projMat]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  have h_mem : (V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)) x ∈ V :=
    Submodule.starProjection_apply_mem V x
  have h_proj : (U.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)).toLinearMap
      ((Matrix.toEuclideanLin Θstar) ((V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap x)) =
      (Matrix.toEuclideanLin Θstar) ((V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap x) :=
    h_UT _ h_mem
  rw [h_proj]

lemma sum_split_Ico {d₁ d₂ : ℕ} (f : ℕ → ℝ) (r : ℕ)
    (hrd : r ≤ min d₁ d₂)
    (hf_zero : ∀ j, min d₁ d₂ ≤ j → f j = 0) :
    (∑ i : Fin d₂, if i.val < r then 0 else f i.val) =
      ∑ j ∈ Finset.Ico r (min d₁ d₂), f j := by
  have hr_d2 : r ≤ d₂ := le_trans hrd (min_le_right d₁ d₂)
  have h_min_d2 : min d₁ d₂ ≤ d₂ := min_le_right d₁ d₂
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < r then 0 else f j) d₂]
  rw [← Finset.sum_range_add_sum_Ico _ hr_d2]
  have h_range_zero : ∑ j ∈ Finset.range r, (if j < r then (0 : ℝ) else f j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_pos hj]
  rw [h_range_zero, zero_add]
  have h_Ico_eq : ∑ j ∈ Finset.Ico r d₂, (if j < r then (0 : ℝ) else f j) =
      ∑ j ∈ Finset.Ico r d₂, f j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [if_neg (not_lt.mpr hj.1)]
  rw [h_Ico_eq]
  rw [← Finset.sum_Ico_consecutive _ hrd h_min_d2]
  have h_tail_zero : ∑ j ∈ Finset.Ico (min d₁ d₂) d₂, f j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    exact hf_zero j hj.1
  rw [h_tail_zero, add_zero]

theorem exists_top_r_singular_subspaces {d₁ d₂ : ℕ} (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂) :
    ∃ (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))),
      Module.finrank ℝ U ≤ r ∧ Module.finrank ℝ V ≤ r ∧
      nucNorm (projMperp U V Θstar) ≤ ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar ∧
      (∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, projMbar U V Δ ∈ Mbar U V) ∧
      (∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, frobSq (projMbar U V Δ) ≤ frobSq Δ) := by
  have hr_d2 : r ≤ d₂ := le_trans hrd (min_le_right d₁ d₂)
  set T := Matrix.toEuclideanLin Θstar
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set hS := T.isSymmetric_adjoint_comp_self
  set b := hS.eigenvectorBasis hn
  let emb : Fin r ↪ Fin d₂ := ⟨Fin.castLE hr_d2, Fin.castLE_injective hr_d2⟩
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)) := Submodule.span ℝ (Set.range fun (i : Fin r) => b (emb i))
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)) := Submodule.map T V
  refine ⟨U, V, ?_⟩
  have h_basis_proj : ∀ (i : Fin d₂),
      (i.val < r → V.starProjection (b i) = b i) ∧
      (r ≤ i.val → V.starProjection (b i) = 0) := by
    intro i
    constructor
    · intro hi
      have h_mem : b i ∈ V := by
        apply Submodule.subset_span
        refine ⟨⟨i.val, hi⟩, ?_⟩
        rfl
      exact Submodule.starProjection_eq_self_iff.mpr h_mem
    · intro hi
      have h_ortho : b i ∈ Vᗮ := by
        rw [Submodule.mem_orthogonal]
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx =>
          rcases hx with ⟨j, rfl⟩
          have hne : emb j ≠ i := by
            intro heq
            have : (emb j).val = i.val := congr_arg Fin.val heq
            dsimp [emb] at this
            omega
          rw [real_inner_comm]
          exact b.orthonormal.2 hne.symm
        | zero => rw [inner_zero_left]
        | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
        | smul c x hx ih => rw [inner_smul_left, ih, mul_zero]
      exact (Submodule.starProjection_apply_eq_zero_iff V).mpr h_ortho
  have hV_rank : Module.finrank ℝ V ≤ r := by
    have hli : LinearIndependent ℝ b := b.orthonormal.linearIndependent
    have hli_v : LinearIndependent ℝ (fun (i : Fin r) => b (emb i)) :=
      hli.comp emb.toFun emb.injective
    have hdim : Module.finrank ℝ V = Fintype.card (Fin r) := by
      rw [finrank_span_eq_card hli_v]
    rw [hdim, Fintype.card_fin]
  have hU_rank : Module.finrank ℝ U ≤ r := by
    have h_map := Submodule.finrank_map_le T V
    exact le_trans h_map hV_rank
  refine ⟨hU_rank, hV_rank, ?_, ?_, ?_⟩
  · -- Nuclear norm bound
    have h_UT : ∀ x ∈ V, (U.starProjection : EuclideanSpace ℝ (Fin d₁) →L[ℝ] EuclideanSpace ℝ (Fin d₁)) (T x) = T x := by
      intro x hx
      have h_mem : T x ∈ U := Submodule.mem_map_of_mem hx
      exact Submodule.starProjection_eq_self_iff.mpr h_mem
    have h_TM_lin : Matrix.toEuclideanLin (projMperp U V Θstar) =
        T.comp (LinearMap.id - (V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap) :=
      toEuclideanLin_projMperp Θstar U V h_UT
    set M := projMperp U V Θstar
    set TM := Matrix.toEuclideanLin M
    set W := polarU M
    have hW_le : ∀ x, ‖W x‖ ≤ ‖x‖ := norm_polarU_le M
    have h_nuc_tr : nucNorm M = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) (TM.adjoint.comp W) :=
      (trace_adjoint_comp_polarU_eq_nucNorm M).symm
    rw [h_nuc_tr, ← sum_inner_eq_trace TM W b]
    have h_term_bound : ∀ (i : Fin d₂),
        @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (W (b i)) ≤
          if i.val < r then 0 else singVal i.val Θstar := by
      intro i
      have h_TM_b : TM (b i) = if i.val < r then 0 else T (b i) := by
        rw [h_TM_lin]
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        have h_proj_eq : (V.starProjection : EuclideanSpace ℝ (Fin d₂) →L[ℝ] EuclideanSpace ℝ (Fin d₂)).toLinearMap (b i) =
            V.starProjection (b i) := rfl
        by_cases hi : i.val < r
        · rw [if_pos hi]
          have h_proj := (h_basis_proj i).1 hi
          rw [h_proj_eq, h_proj, sub_self, map_zero]
        · rw [if_neg hi]
          have hi_ge : r ≤ i.val := not_lt.mp hi
          have h_proj := (h_basis_proj i).2 hi_ge
          rw [h_proj_eq, h_proj, sub_zero]
      by_cases hi : i.val < r
      · rw [if_pos hi, h_TM_b, if_pos hi, inner_zero_left]
      · rw [if_neg hi, h_TM_b, if_neg hi]
        have h_cs := real_inner_le_norm (T (b i)) (W (b i))
        have hW_norm : ‖W (b i)‖ ≤ 1 := by
          have := hW_le (b i)
          rw [b.orthonormal.1 i] at this
          exact this
        have h_norm_T : ‖T (b i)‖ = singVal i.val Θstar := by
          dsimp [singVal]
          exact norm_toEuclideanLin_apply_eigenvectorBasis Θstar i
        rw [h_norm_T] at h_cs
        refine h_cs.trans ?_
        have h_pos : 0 ≤ singVal i.val Θstar := (Matrix.toEuclideanLin Θstar).singularValues_nonneg i.val
        have := mul_le_mul_of_nonneg_left hW_norm h_pos
        rwa [mul_one] at this
    have h_sum_le : (∑ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (W (b i))) ≤
        ∑ i : Fin d₂, if i.val < r then (0 : ℝ) else singVal i.val Θstar :=
      Finset.sum_le_sum fun i _ => h_term_bound i
    refine h_sum_le.trans ?_
    have h_split := sum_split_Ico (fun j => singVal j Θstar) r hrd (fun j hj => singularValues_eq_zero_of_min_le Θstar j hj)
    rw [h_split]
  · -- projMbar U V Δ ∈ Mbar U V
    intro Δ
    exact projMbar_mem_Mbar U V Δ
  · -- frobSq (projMbar U V Δ) ≤ frobSq Δ
    intro Δ
    exact frobSq_projMbar_le U V Δ

end WainwrightHDS.NucNorm

open WainwrightHDS.NucNorm

theorem solution {d₁ d₂ : ℕ} (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂) :
    ∃ (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))),
      Module.finrank ℝ U ≤ r ∧ Module.finrank ℝ V ≤ r ∧
      nucNorm (projMperp U V Θstar) ≤ ∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar ∧
      (∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, projMbar U V Δ ∈ Mbar U V) ∧
      (∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, frobSq (projMbar U V Δ) ≤ frobSq Δ) :=
  WainwrightHDS.NucNorm.exists_top_r_singular_subspaces Θstar r hr₁ hrd

