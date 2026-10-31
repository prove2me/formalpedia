-- Prove2me | solution 1 for WainwrightHDS.NucNorm.isLUB_traceInner_nucNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T03:23:55.584001+00:00
-- url     : https://prove2.me/submissions/62ceab25-85f7-4851-bffb-a65e97660440

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace WainwrightHDS.NucNorm

lemma traceInner_eq_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = (A.transpose * B).trace := by
  dsimp [traceInner, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

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

lemma trace_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ n) (Matrix.toEuclideanLin A) = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun n ℝ).toBasis

lemma traceInner_eq_linearMap_trace {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂))
      ((Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin B)) := by
  rw [traceInner_eq_trace]
  rw [← trace_toEuclideanLin]
  rw [toEuclideanLin_mul, toEuclideanLin_transpose]

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

theorem traceInner_le_opNorm2 {d₁ d₂ : ℕ} (M N : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hM : nucNorm M ≤ 1) :
    traceInner M N ≤ opNorm2 N := by
  set TM := Matrix.toEuclideanLin M
  set TN := Matrix.toEuclideanLin N
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TM.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  have h_trace : traceInner M N = ∑ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TN (b i)) := by
    rw [traceInner_eq_linearMap_trace M N]
    rw [LinearMap.trace_eq_sum_inner (TM.adjoint.comp TN) b]
    refine Fintype.sum_congr _ _ fun i => ?_
    exact LinearMap.adjoint_inner_right TM (b i) (TN (b i))
  have h_term_le : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TN (b i)) ≤
      TM.singularValues i * opNorm2 N := by
    intro i
    have h_cs := real_inner_le_norm (TM (b i)) (TN (b i))
    have h_norm_TM : ‖TM (b i)‖ = TM.singularValues i := norm_toEuclideanLin_apply_eigenvectorBasis M i
    have h_norm_TN : ‖TN (b i)‖ ≤ opNorm2 N := by
      dsimp [opNorm2]
      have := ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap TN) (b i)
      have hb_one : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [hb_one, mul_one] at this
      exact this
    rw [h_norm_TM] at h_cs
    refine h_cs.trans ?_
    have h_pos : 0 ≤ TM.singularValues (i : ℕ) := TM.singularValues_nonneg i
    exact mul_le_mul_of_nonneg_left h_norm_TN h_pos
  have h_sum_le : (∑ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TM (b i)) (TN (b i))) ≤
      ∑ i : Fin d₂, TM.singularValues i * opNorm2 N :=
    Finset.sum_le_sum fun i _ => h_term_le i
  rw [← Finset.sum_mul] at h_sum_le
  rw [sum_singularValues_eq_nucNorm M] at h_sum_le
  have h_op_nonneg : 0 ≤ opNorm2 N := norm_nonneg _
  have h_le_one : nucNorm M * opNorm2 N ≤ 1 * opNorm2 N := by
    nlinarith
  rw [one_mul] at h_le_one
  exact h_trace.symm ▸ (h_sum_le.trans h_le_one)

lemma euclideanSpace_inner_eq {n : Type*} [Fintype n] (x y : EuclideanSpace ℝ n) :
    @inner ℝ (EuclideanSpace ℝ n) _ x y = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

lemma toEuclideanLin_apply_apply {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ)
    (v : EuclideanSpace ℝ (Fin d₂)) (i : Fin d₁) :
    Matrix.toEuclideanLin M v i = ∑ j, M i j * v j :=
  rfl

def rankOneMat {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂)) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  fun i j => u i * v j

lemma toEuclideanLin_rankOneMat {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂))
    (w : EuclideanSpace ℝ (Fin d₂)) :
    Matrix.toEuclideanLin (rankOneMat u v) w = @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ v w • u := by
  ext i
  rw [toEuclideanLin_apply_apply, euclideanSpace_inner_eq]
  dsimp [rankOneMat]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

lemma traceInner_rankOneMat {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂))
    (N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (rankOneMat u v) N = @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ u (Matrix.toEuclideanLin N v) := by
  dsimp [traceInner, rankOneMat]
  rw [euclideanSpace_inner_eq]
  congr 1; ext i
  rw [toEuclideanLin_apply_apply]
  rw [Finset.mul_sum]
  congr 1; ext j
  ring

lemma singularValues_rankOneMat_zero_le_one {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂))
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    (Matrix.toEuclideanLin (rankOneMat u v)).singularValues 0 ≤ 1 := by
  by_cases hd₂ : d₂ = 0
  · subst hd₂
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) ≤ 0 := by simp [finrank_euclideanSpace]
    rw [(Matrix.toEuclideanLin (rankOneMat u v)).singularValues_of_finrank_le hfin]
    exact zero_le_one
  · have h0 : 0 < d₂ := Nat.pos_of_ne_zero hd₂
    let i0 : Fin d₂ := ⟨0, h0⟩
    set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
    set b := ((Matrix.toEuclideanLin (rankOneMat u v)).isSymmetric_adjoint_comp_self).eigenvectorBasis hn
    have h_sv := norm_toEuclideanLin_apply_eigenvectorBasis (rankOneMat u v) i0
    rw [← h_sv]
    rw [toEuclideanLin_rankOneMat]
    rw [norm_smul]
    have hb1 : ‖b i0‖ = 1 := b.orthonormal.1 i0
    have h_inner_le : |@inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ v (b i0)| ≤ 1 := by
      have hcs := abs_real_inner_le_norm v (b i0)
      rw [hb1, mul_one] at hcs
      exact hcs.trans hv
    have := mul_le_mul h_inner_le hu (norm_nonneg u) zero_le_one
    rwa [mul_one] at this

lemma finrank_range_rankOneMat_le_one {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂)) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin (rankOneMat u v))) ≤ 1 := by
  set T := Matrix.toEuclideanLin (rankOneMat u v)
  have h_range : LinearMap.range T ≤ Submodule.span ℝ {u} := by
    rintro x ⟨w, rfl⟩
    rw [toEuclideanLin_rankOneMat]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have h_span : Module.finrank ℝ (Submodule.span ℝ {u}) ≤ 1 := by
    by_cases hu : u = 0
    · rw [hu, Submodule.span_zero_singleton]
      simp
    · rw [finrank_span_singleton hu]
  exact (Submodule.finrank_mono h_range).trans h_span

lemma singularValues_rankOneMat_of_ge_one {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂))
    (j : ℕ) (hj : 1 ≤ j) :
    (Matrix.toEuclideanLin (rankOneMat u v)).singularValues j = 0 := by
  have h_le := (finrank_range_rankOneMat_le_one u v).trans hj
  exact (Matrix.toEuclideanLin (rankOneMat u v)).singularValues_eq_zero_iff_le_finrank_range.mpr h_le

lemma nucNorm_rankOneMat_le_one {d₁ d₂ : ℕ} (u : EuclideanSpace ℝ (Fin d₁)) (v : EuclideanSpace ℝ (Fin d₂))
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    nucNorm (rankOneMat u v) ≤ 1 := by
  dsimp [nucNorm, singVal]
  by_cases h0 : min d₁ d₂ = 0
  · rw [h0, Finset.range_zero, Finset.sum_empty]
    exact zero_le_one
  · have h_pos : 0 < min d₁ d₂ := Nat.pos_of_ne_zero h0
    have h_split : Finset.range (min d₁ d₂) = insert 0 (Finset.Ico 1 (min d₁ d₂)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h_split, Finset.sum_insert]
    · have h_zero : ∑ j ∈ Finset.Ico 1 (min d₁ d₂), (Matrix.toEuclideanLin (rankOneMat u v)).singularValues j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        exact singularValues_rankOneMat_of_ge_one u v j hj.1
      rw [h_zero, add_zero]
      exact singularValues_rankOneMat_zero_le_one u v hu hv
    · simp

lemma nucNorm_zero {d₁ d₂ : ℕ} : nucNorm (0 : Matrix (Fin d₁) (Fin d₂) ℝ) = 0 := by
  dsimp [nucNorm, singVal]
  have h_zero : Matrix.toEuclideanLin (0 : Matrix (Fin d₁) (Fin d₂) ℝ) = 0 := map_zero _
  rw [h_zero]
  simp

lemma traceInner_zero_left {d₁ d₂ : ℕ} (N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner 0 N = 0 := by
  dsimp [traceInner]
  simp

lemma opNorm2_le_of_mem_upperBounds {d₁ d₂ : ℕ} (N : Matrix (Fin d₁) (Fin d₂) ℝ)
    (b : ℝ) (hb : b ∈ upperBounds {t : ℝ | ∃ M : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M ≤ 1 ∧ t = traceInner M N}) :
    opNorm2 N ≤ b := by
  have hb0 : 0 ≤ b := by
    have h_mem : (0 : ℝ) ∈ {t : ℝ | ∃ M : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M ≤ 1 ∧ t = traceInner M N} := by
      refine ⟨0, ?_, (traceInner_zero_left N).symm⟩
      rw [nucNorm_zero]
      exact zero_le_one
    exact hb h_mem
  dsimp [opNorm2]
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun x => ?_
  change ‖(Matrix.toEuclideanLin N) x‖ ≤ b * ‖x‖
  by_cases hx : x = 0
  · subst hx
    simp
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_norm_ne : ‖x‖ ≠ 0 := hx_norm_pos.ne'
  set v := ‖x‖⁻¹ • x
  have hv_norm : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx_norm_ne]
  set y := Matrix.toEuclideanLin N v
  have hx_eq : x = ‖x‖ • v := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hx_norm_ne, one_smul]
  have h_TN_x : Matrix.toEuclideanLin N x = ‖x‖ • y := by
    rw [congr_arg (Matrix.toEuclideanLin N) hx_eq, map_smul]
  by_cases hy : y = 0
  · have h_zero : Matrix.toEuclideanLin N x = 0 := by
      rw [h_TN_x, hy, smul_zero]
    rw [h_zero, norm_zero]
    positivity
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hy_norm_ne : ‖y‖ ≠ 0 := hy_norm_pos.ne'
  set u := ‖y‖⁻¹ • y
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy_norm_ne]
  set M := rankOneMat u v
  have hM_nuc : nucNorm M ≤ 1 := nucNorm_rankOneMat_le_one u v hu_norm.le hv_norm.le
  have hM_trace : traceInner M N = ‖y‖ := by
    rw [traceInner_rankOneMat]
    dsimp [u]
    rw [inner_smul_left]
    have : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ y y = ‖y‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
    rw [conj_trivial, this, sq]
    rw [← mul_assoc, inv_mul_cancel₀ hy_norm_ne, one_mul]
  have hy_le_b : ‖y‖ ≤ b := by
    have h_mem : ‖y‖ ∈ {t : ℝ | ∃ M : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M ≤ 1 ∧ t = traceInner M N} :=
      ⟨M, hM_nuc, hM_trace.symm⟩
    exact hb h_mem
  rw [h_TN_x, norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
  calc ‖x‖ * ‖y‖
    _ ≤ ‖x‖ * b := mul_le_mul_of_nonneg_left hy_le_b (norm_nonneg x)
    _ = b * ‖x‖ := mul_comm _ _

theorem isLUB_traceInner_nucNorm_le_one {d₁ d₂ : ℕ} (N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    IsLUB {t : ℝ | ∃ M : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M ≤ 1 ∧ t = traceInner M N}
      (opNorm2 N) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    rcases ht with ⟨M, hM, rfl⟩
    exact traceInner_le_opNorm2 M N hM
  · intro b hb
    exact opNorm2_le_of_mem_upperBounds N b hb

abbrev solution := @isLUB_traceInner_nucNorm_le_one

end WainwrightHDS.NucNorm

abbrev solution := @WainwrightHDS.NucNorm.isLUB_traceInner_nucNorm_le_one
