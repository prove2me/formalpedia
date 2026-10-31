-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nucNorm_add_of_mem_Mspace_of_mem_MbarPerp
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T03:40:18.703775+00:00
-- url     : https://prove2.me/submissions/0c1b63d5-5bb2-4220-b2d4-f3b14f108b19

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_Mspace
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp
import Definitions.Def_WainwrightHDS_NucNorm_Mbar
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace WainwrightHDS.NucNorm

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

lemma toEuclideanLin_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    Matrix.toEuclideanLin A.transpose = (Matrix.toEuclideanLin A).adjoint := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

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

theorem trace_adjoint_comp_le_nucNorm {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ)
    (U : EuclideanSpace ℝ (Fin d₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁))
    (hU : ∀ x, ‖U x‖ ≤ ‖x‖) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin M).adjoint.comp U) ≤ nucNorm M := by
  set TM := Matrix.toEuclideanLin M
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  rw [← sum_inner_eq_trace TM U b]
  have h_term_le : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (U (b i)) ≤
      TM.singularValues i := by
    intro i
    have h_cs := real_inner_le_norm (TM (b i)) (U (b i))
    have h_norm_TM : ‖TM (b i)‖ = TM.singularValues i := norm_toEuclideanLin_apply_eigenvectorBasis M i
    have h_norm_U : ‖U (b i)‖ ≤ 1 := by
      have := hU (b i)
      have hb_one : ‖b i‖ = 1 := b.orthonormal.1 i
      rwa [hb_one] at this
    rw [h_norm_TM] at h_cs
    refine h_cs.trans ?_
    have h_pos : 0 ≤ TM.singularValues (i : ℕ) := TM.singularValues_nonneg i
    have := mul_le_mul_of_nonneg_left h_norm_U h_pos
    rwa [mul_one] at this
  have h_sum_le : (∑ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (U (b i))) ≤
      ∑ i : Fin d₂, TM.singularValues i :=
    Finset.sum_le_sum fun i _ => h_term_le i
  rwa [sum_singularValues_eq_nucNorm M] at h_sum_le

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

theorem makeU_mem_submodule {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) (S : Submodule ℝ E₁)
    (hu : ∀ i, u i ∈ S) (x : E₂) :
    makeU b u x ∈ S := by
  rw [makeU_apply]
  exact Submodule.sum_mem S fun j _ => Submodule.smul_mem S _ (hu j)

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

lemma polarVec_mem_submodule {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin d₂)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (hS : LinearMap.range (Matrix.toEuclideanLin M) ≤ S) :
    polarVec M i ∈ S := by
  dsimp [polarVec]
  set TM := Matrix.toEuclideanLin M
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  split_ifs with hi
  · exact Submodule.zero_mem S
  · exact Submodule.smul_mem S _ (hS (LinearMap.mem_range_self TM (b i)))

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

lemma polarU_mem_submodule {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (hS : LinearMap.range (Matrix.toEuclideanLin M) ≤ S)
    (x : EuclideanSpace ℝ (Fin d₂)) :
    polarU M x ∈ S := by
  dsimp [polarU]
  exact makeU_mem_submodule _ (polarVec M) S (fun i => polarVec_mem_submodule M i S hS) x

lemma eigenvector_mem_V_of_norm_ne_zero {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (hA_row : LinearMap.range (Matrix.toEuclideanLin A.transpose) ≤ V)
    (i : Fin d₂)
    (h_ne : ‖Matrix.toEuclideanLin A (((Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self).eigenvectorBasis
      (by simp [finrank_euclideanSpace] : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂) i)‖ ≠ 0) :
    (((Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self).eigenvectorBasis
      (by simp [finrank_euclideanSpace] : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂) i) ∈ V := by
  set TA := Matrix.toEuclideanLin A
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set hS := TA.isSymmetric_adjoint_comp_self
  set bA := hS.eigenvectorBasis hn
  set ev := hS.eigenvalues hn i
  have h_adj : TA.adjoint = Matrix.toEuclideanLin A.transpose := (toEuclideanLin_transpose A).symm
  have h_eig : (TA.adjoint ∘ₗ TA) (bA i) = ev • bA i := hS.apply_eigenvectorBasis hn i
  have h_in_range : (TA.adjoint ∘ₗ TA) (bA i) ∈ V := by
    change TA.adjoint (TA (bA i)) ∈ V
    rw [h_adj]
    exact hA_row (LinearMap.mem_range_self _ (TA (bA i)))
  rw [h_eig] at h_in_range
  have h_sq_sing : TA.singularValues i ^ 2 = ev := TA.sq_singularValues_fin hn i
  have h_sv : ‖TA (bA i)‖ = TA.singularValues i := norm_toEuclideanLin_apply_eigenvectorBasis A i
  have hev_pos : 0 < ev := by
    rw [← h_sq_sing, ← h_sv]
    exact sq_pos_of_ne_zero h_ne
  have hev_ne : ev ≠ 0 := hev_pos.ne'
  have h_smul : ev⁻¹ • (ev • bA i) ∈ V := Submodule.smul_mem V ev⁻¹ h_in_range
  rwa [inv_smul_smul₀ hev_ne] at h_smul

theorem inner_TA_polarU_proj_eq_singVal {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (hA_row : LinearMap.range (Matrix.toEuclideanLin A.transpose) ≤ V)
    (i : Fin d₂) :
    let TA := Matrix.toEuclideanLin A
    let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
    let bA := (TA.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
    @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TA (bA i)) (polarU A (V.starProjection (bA i))) =
      TA.singularValues i := by
  dsimp only
  set TA := Matrix.toEuclideanLin A
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set bA := (TA.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  have h_sv := norm_toEuclideanLin_apply_eigenvectorBasis A i
  by_cases h_zero : ‖TA (bA i)‖ = 0
  · have hTA_zero : TA (bA i) = 0 := norm_eq_zero.mp h_zero
    rw [hTA_zero, inner_zero_left, ← h_sv, h_zero]
  · have h_mem : bA i ∈ V := eigenvector_mem_V_of_norm_ne_zero A V hA_row i h_zero
    have h_proj : V.starProjection (bA i) = bA i := Submodule.starProjection_eq_self_iff.mpr h_mem
    rw [h_proj, polarU_basis A i]
    exact polarVec_inner_eval A i

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

theorem nucNorm_add_le_self {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (A + B) ≤ nucNorm A + nucNorm B := by
  set W := polarU (A + B)
  have hW_le : ∀ x, ‖W x‖ ≤ ‖x‖ := norm_polarU_le (A + B)
  rw [← trace_adjoint_comp_polarU_eq_nucNorm (A + B)]
  have h_toLin_add : Matrix.toEuclideanLin (A + B) = Matrix.toEuclideanLin A + Matrix.toEuclideanLin B :=
    map_add (Matrix.toEuclideanLin) A B
  have h_adj_add : (Matrix.toEuclideanLin (A + B)).adjoint =
      (Matrix.toEuclideanLin A).adjoint + (Matrix.toEuclideanLin B).adjoint := by
    rw [h_toLin_add, map_add LinearMap.adjoint]
  rw [h_adj_add, LinearMap.add_comp, map_add (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)))]
  have hA_le := trace_adjoint_comp_le_nucNorm A W hW_le
  have hB_le := trace_adjoint_comp_le_nucNorm B W hW_le
  linarith

noncomputable def makeW {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) :
    EuclideanSpace ℝ (Fin d₂) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁) :=
  (polarU A).comp V.starProjection.toLinearMap + (polarU B).comp Vᗮ.starProjection.toLinearMap

theorem norm_makeW_le {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (hA_col : LinearMap.range (Matrix.toEuclideanLin A) ≤ U)
    (hB_col : LinearMap.range (Matrix.toEuclideanLin B) ≤ Uᗮ)
    (x : EuclideanSpace ℝ (Fin d₂)) :
    ‖makeW A B V x‖ ≤ ‖x‖ := by
  dsimp [makeW]
  set u₁ := polarU A (V.starProjection x)
  set u₂ := polarU B (Vᗮ.starProjection x)
  have hu₁ : u₁ ∈ U := polarU_mem_submodule A U hA_col (V.starProjection x)
  have hu₂ : u₂ ∈ Uᗮ := polarU_mem_submodule B Uᗮ hB_col (Vᗮ.starProjection x)
  have h_ortho : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ u₁ u₂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu₁ hu₂
  have h_pyth : ‖u₁ + u₂‖ ^ 2 = ‖u₁‖ ^ 2 + ‖u₂‖ ^ 2 := by
    simp_rw [sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u₁ u₂ h_ortho
  have hu₁_le : ‖u₁‖ ^ 2 ≤ ‖V.starProjection x‖ ^ 2 := by
    have := norm_polarU_le A (V.starProjection x)
    nlinarith [norm_nonneg u₁, norm_nonneg (V.starProjection x)]
  have hu₂_le : ‖u₂‖ ^ 2 ≤ ‖Vᗮ.starProjection x‖ ^ 2 := by
    have := norm_polarU_le B (Vᗮ.starProjection x)
    nlinarith [norm_nonneg u₂, norm_nonneg (Vᗮ.starProjection x)]
  have h_sum_le : ‖u₁ + u₂‖ ^ 2 ≤ ‖V.starProjection x‖ ^ 2 + ‖Vᗮ.starProjection x‖ ^ 2 := by
    linarith
  have h_dec : x = V.starProjection x + Vᗮ.starProjection x :=
    (Submodule.starProjection_add_starProjection_orthogonal x).symm
  have h_ortho_x : @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ (V.starProjection x) (Vᗮ.starProjection x) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem V x)
      (Submodule.starProjection_apply_mem Vᗮ x)
  have h_x_pyth : ‖x‖ ^ 2 = ‖V.starProjection x‖ ^ 2 + ‖Vᗮ.starProjection x‖ ^ 2 := by
    nth_rw 1 [h_dec]
    simp_rw [sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_ortho_x
  rw [← h_x_pyth] at h_sum_le
  have h1 : 0 ≤ ‖u₁ + u₂‖ := norm_nonneg _
  have h2 : 0 ≤ ‖x‖ := norm_nonneg _
  have h_sqrt := Real.sqrt_le_sqrt h_sum_le
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at h_sqrt

theorem trace_adjoint_comp_makeW_A {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (hA : A ∈ Mspace U V) (hB : B ∈ MbarPerp U V) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin A).adjoint.comp (makeW A B V)) =
      nucNorm A := by
  rcases hA with ⟨hA_row, hA_col⟩
  rcases hB with ⟨hB_row, hB_col⟩
  set TA := Matrix.toEuclideanLin A
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set bA := (TA.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  rw [← sum_inner_eq_trace TA (makeW A B V) bA]
  have h_term : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TA (bA i)) (makeW A B V (bA i)) =
      TA.singularValues i := by
    intro i
    change @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TA (bA i))
      (polarU A (V.starProjection (bA i)) + polarU B (Vᗮ.starProjection (bA i))) = TA.singularValues i
    rw [inner_add_right]
    have h_ortho_B : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TA (bA i))
        (polarU B (Vᗮ.starProjection (bA i))) = 0 := by
      have h1 : TA (bA i) ∈ U := hA_col (LinearMap.mem_range_self TA (bA i))
      have h2 : polarU B (Vᗮ.starProjection (bA i)) ∈ Uᗮ :=
        polarU_mem_submodule B Uᗮ hB_col (Vᗮ.starProjection (bA i))
      exact Submodule.inner_right_of_mem_orthogonal h1 h2
    rw [h_ortho_B, add_zero]
    exact inner_TA_polarU_proj_eq_singVal A V hA_row i
  simp_rw [h_term]
  exact sum_singularValues_eq_nucNorm A

theorem trace_adjoint_comp_makeW_B {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (hA : A ∈ Mspace U V) (hB : B ∈ MbarPerp U V) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin B).adjoint.comp (makeW A B V)) =
      nucNorm B := by
  rcases hA with ⟨hA_row, hA_col⟩
  rcases hB with ⟨hB_row, hB_col⟩
  set TB := Matrix.toEuclideanLin B
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set bB := (TB.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  rw [← sum_inner_eq_trace TB (makeW A B V) bB]
  have h_term : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TB (bB i)) (makeW A B V (bB i)) =
      TB.singularValues i := by
    intro i
    change @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TB (bB i))
      (polarU A (V.starProjection (bB i)) + polarU B (Vᗮ.starProjection (bB i))) = TB.singularValues i
    rw [inner_add_right]
    have h_ortho_A : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TB (bB i))
        (polarU A (V.starProjection (bB i))) = 0 := by
      have h1 : polarU A (V.starProjection (bB i)) ∈ U :=
        polarU_mem_submodule A U hA_col (V.starProjection (bB i))
      have h2 : TB (bB i) ∈ Uᗮ := hB_col (LinearMap.mem_range_self TB (bB i))
      exact Submodule.inner_left_of_mem_orthogonal h1 h2
    rw [h_ortho_A, zero_add]
    exact inner_TA_polarU_proj_eq_singVal B Vᗮ hB_row i
  simp_rw [h_term]
  exact sum_singularValues_eq_nucNorm B

theorem nucNorm_add_of_mem_Mspace_of_mem_MbarPerp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (A B : Matrix (Fin d₁) (Fin d₂) ℝ) (hA : A ∈ Mspace U V) (hB : B ∈ MbarPerp U V) :
    nucNorm (A + B) = nucNorm A + nucNorm B := by
  have h_le := nucNorm_add_le_self A B
  have h_ge : nucNorm A + nucNorm B ≤ nucNorm (A + B) := by
    set W := makeW A B V
    have hW_le : ∀ x, ‖W x‖ ≤ ‖x‖ := norm_makeW_le A B U V hA.2 hB.2
    have hA_trace := trace_adjoint_comp_makeW_A A B U V hA hB
    have hB_trace := trace_adjoint_comp_makeW_B A B U V hA hB
    have h_toLin_add : Matrix.toEuclideanLin (A + B) = Matrix.toEuclideanLin A + Matrix.toEuclideanLin B :=
      map_add (Matrix.toEuclideanLin) A B
    have h_adj_add : (Matrix.toEuclideanLin (A + B)).adjoint =
        (Matrix.toEuclideanLin A).adjoint + (Matrix.toEuclideanLin B).adjoint := by
      rw [h_toLin_add, map_add LinearMap.adjoint]
    have h_trace_sum : nucNorm A + nucNorm B =
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) (((Matrix.toEuclideanLin (A + B)).adjoint).comp W) := by
      rw [← hA_trace, ← hB_trace, ← map_add (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂))),
          ← LinearMap.add_comp, ← h_adj_add]
    rw [h_trace_sum]
    exact trace_adjoint_comp_le_nucNorm (A + B) W hW_le
  exact le_antisymm h_le h_ge

abbrev solution := @nucNorm_add_of_mem_Mspace_of_mem_MbarPerp

end WainwrightHDS.NucNorm

abbrev solution := @WainwrightHDS.NucNorm.nucNorm_add_of_mem_Mspace_of_mem_MbarPerp
