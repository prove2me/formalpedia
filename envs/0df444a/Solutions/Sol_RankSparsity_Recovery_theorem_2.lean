-- Prove2me | solution 1 for RankSparsity.Recovery.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T08:15:38.529899+00:00
-- url     : https://prove2.me/submissions/e96d1aea-9280-4c08-8189-718b4b41e35c

import Mathlib
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_RankSparsity_Recovery_Setup

open MatrixCompletion
open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof
end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def matrixCLM {n : ℕ} (X : RealMatrix n n) : Euclid n →L[ℝ] Euclid n :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)

lemma spectral_eq_norm {n : ℕ} (X : RealMatrix n n) :
    spectralNorm X = ‖matrixCLM X‖ := rfl

lemma matrixCLM_injective {n : ℕ} : Function.Injective (@matrixCLM n) := by
  intro X Y h
  apply (Matrix.toLpLin 2 2).injective
  exact congrArg ContinuousLinearMap.toLinearMap h

@[simp] lemma matrixCLM_zero {n : ℕ} : matrixCLM (0 : RealMatrix n n) = 0 := by
  ext x i
  simp [matrixCLM, Matrix.toEuclideanLin]

@[simp] lemma matrixCLM_add {n : ℕ} (X Y : RealMatrix n n) :
    matrixCLM (X + Y) = matrixCLM X + matrixCLM Y := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (X + Y) x = _
  rw [map_add]
  rfl

@[simp] lemma matrixCLM_smul {n : ℕ} (c : ℝ) (X : RealMatrix n n) :
    matrixCLM (c • X) = c • matrixCLM X := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (c • X) x = _
  rw [map_smul]
  rfl

lemma matrixCLM_mul {n : ℕ} (X Y : RealMatrix n n) :
    matrixCLM (X * Y) = (matrixCLM X).comp (matrixCLM Y) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 2 2 (X * Y) x = _
  rw [Matrix.toLpLin_mul_same]
  rfl

lemma spectral_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ spectralNorm X := norm_nonneg _

lemma spectral_eq_zero_iff {n : ℕ} (X : RealMatrix n n) :
    spectralNorm X = 0 ↔ X = 0 := by
  rw [spectral_eq_norm, norm_eq_zero]
  constructor
  · intro h
    apply matrixCLM_injective
    simpa using h
  · rintro rfl
    exact matrixCLM_zero

lemma spectral_add_le {n : ℕ} (X Y : RealMatrix n n) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  simp only [spectral_eq_norm, matrixCLM_add]
  exact norm_add_le _ _

lemma spectral_smul {n : ℕ} (c : ℝ) (X : RealMatrix n n) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  simp [spectral_eq_norm, norm_smul, Real.norm_eq_abs]

lemma spectral_mul_le {n : ℕ} (X Y : RealMatrix n n) :
    spectralNorm (X * Y) ≤ spectralNorm X * spectralNorm Y := by
  simp only [spectral_eq_norm, matrixCLM_mul]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

noncomputable def singularBasis {n : ℕ} (X : RealMatrix n n) :
    OrthonormalBasis (Fin n) ℝ (Euclid n) :=
  (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis
    finrank_euclideanSpace_fin

noncomputable def singularValue {n : ℕ} (X : RealMatrix n n) (i : Fin n) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues i

lemma singularValue_nonneg {n : ℕ} (X : RealMatrix n n) (i : Fin n) :
    0 ≤ singularValue X i := LinearMap.singularValues_nonneg _ _

lemma singular_image_inner {n : ℕ} (X : RealMatrix n n) (i j : Fin n) :
    inner ℝ (matrixCLM X (singularBasis X i)) (matrixCLM X (singularBasis X j)) =
      if i = j then (singularValue X i)^2 else 0 := by
  change inner ℝ (Matrix.toEuclideanLin X (singularBasis X i))
    (Matrix.toEuclideanLin X (singularBasis X j)) = _
  rw [← LinearMap.adjoint_inner_right]
  have he := (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
    finrank_euclideanSpace_fin j
  change (Matrix.toEuclideanLin X).adjoint
    (Matrix.toEuclideanLin X (singularBasis X j)) = _ at he
  rw [he, inner_smul_right]
  change _ * inner ℝ (singularBasis X i) (singularBasis X j) = _
  have hi := (singularBasis X).inner_eq_ite i j
  rw [hi]
  split_ifs with h
  · subst j
    simp only [mul_one]
    exact ((Matrix.toEuclideanLin X).sq_singularValues_fin finrank_euclideanSpace_fin i).symm
  · simp

lemma singular_image_norm {n : ℕ} (X : RealMatrix n n) (i : Fin n) :
    ‖matrixCLM X (singularBasis X i)‖ = singularValue X i := by
  have h := singular_image_inner X i i
  rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (matrixCLM X (singularBasis X i)), singularValue_nonneg X i]

noncomputable def leftSingularVector {n : ℕ} (X : RealMatrix n n) (i : Fin n) : Euclid n :=
  (singularValue X i)⁻¹ • matrixCLM X (singularBasis X i)

lemma singular_image_eq {n : ℕ} (X : RealMatrix n n) (i : Fin n) :
    matrixCLM X (singularBasis X i) = singularValue X i • leftSingularVector X i := by
  by_cases h : singularValue X i = 0
  · have hz : matrixCLM X (singularBasis X i) = 0 := by
      apply norm_eq_zero.mp
      rw [singular_image_norm, h]
    simp [h, hz]
  · simp [leftSingularVector, smul_smul, h]

lemma leftSingularVector_inner {n : ℕ} (X : RealMatrix n n) (i j : Fin n) :
    inner ℝ (leftSingularVector X i) (leftSingularVector X j) =
      if i = j then (if singularValue X i = 0 then 0 else 1) else 0 := by
  simp only [leftSingularVector, inner_smul_left, inner_smul_right, conj_trivial,
    singular_image_inner]
  by_cases h : i = j
  · subst j
    by_cases hz : singularValue X i = 0
    · simp [hz]
    · simp [hz, pow_two]
  · simp [h]

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

lemma nuclear_eq_sum_singularValue {n : ℕ} (X : RealMatrix n n) :
    nuclearNorm X = ∑ i : Fin n, singularValue X i := by
  unfold nuclearNorm LinearMap.singularValues
  rw [Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  simp only [Finsupp.ofSupportFinite_coe]
  have hn : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  calc
    _ = ∑ i : Fin (Module.finrank ℝ (Euclid n)),
        (Matrix.toEuclideanLin X).singularValues i := by
      apply Finset.sum_congr rfl
      intro i _
      exact ((Matrix.toEuclideanLin X).singularValues_fin rfl i).symm
    _ = _ := Fintype.sum_equiv (finCongr hn) _ _ (by intro i; rfl)

lemma nuclear_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ nuclearNorm X := by
  rw [nuclear_eq_sum_singularValue]
  exact Finset.sum_nonneg fun i _ => singularValue_nonneg X i

lemma nuclear_eq_zero_iff {n : ℕ} (X : RealMatrix n n) : nuclearNorm X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hs : ∀ i, singularValue X i = 0 := by
      rw [nuclear_eq_sum_singularValue] at h
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => singularValue_nonneg X j)).mp h i (Finset.mem_univ i)
    apply matrixCLM_injective
    rw [matrixCLM_zero]
    apply ContinuousLinearMap.ext
    intro x
    rw [← (singularBasis X).sum_repr' x, map_sum]
    simp only [map_smul]
    have hz : ∀ i, matrixCLM X (singularBasis X i) = 0 := by
      intro i
      apply norm_eq_zero.mp
      rw [singular_image_norm, hs i]
    simp [hz]
  · rintro rfl
    rw [nuclear_eq_sum_singularValue]
    apply Finset.sum_eq_zero
    intro i _
    rw [← singular_image_norm]
    simp

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

lemma matrixCLM_apply_inner_row {n : ℕ} (X : RealMatrix n n) (x : Euclid n) (a : Fin n) :
    matrixCLM X x a = inner ℝ (WithLp.toLp 2 (X a)) x := by
  simp [matrixCLM, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma matrixInner_basis {n : ℕ} (W X : RealMatrix n n)
    (b : OrthonormalBasis (Fin n) ℝ (Euclid n)) :
    matrixInner W X = ∑ i, inner ℝ (matrixCLM W (b i)) (matrixCLM X (b i)) := by
  symm
  calc
    ∑ i, inner ℝ (matrixCLM W (b i)) (matrixCLM X (b i)) =
        ∑ i, ∑ a, inner ℝ (WithLp.toLp 2 (W a)) (b i) *
          inner ℝ (b i) (WithLp.toLp 2 (X a)) := by
      apply Finset.sum_congr rfl
      intro i _
      change (∑ a, (matrixCLM X (b i)) a * (matrixCLM W (b i)) a) = _
      apply Finset.sum_congr rfl
      intro a _
      rw [matrixCLM_apply_inner_row, matrixCLM_apply_inner_row]
      rw [real_inner_comm (b i)]
      ring
    _ = ∑ a, ∑ i, inner ℝ (WithLp.toLp 2 (W a)) (b i) *
          inner ℝ (b i) (WithLp.toLp 2 (X a)) := Finset.sum_comm
    _ = ∑ a, inner ℝ (WithLp.toLp 2 (W a)) (WithLp.toLp 2 (X a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact b.sum_inner_mul_inner _ _
    _ = matrixInner W X := by
      simp [matrixInner, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

noncomputable def polarCLM {n : ℕ} (X : RealMatrix n n) : Euclid n →L[ℝ] Euclid n :=
  ∑ i, InnerProductSpace.rankOne ℝ (leftSingularVector X i) (singularBasis X i)

noncomputable def polarMatrix {n : ℕ} (X : RealMatrix n n) : RealMatrix n n :=
  Matrix.toEuclideanLin.symm (polarCLM X).toLinearMap

lemma matrixCLM_polar {n : ℕ} (X : RealMatrix n n) :
    matrixCLM (polarMatrix X) = polarCLM X := by
  apply ContinuousLinearMap.coe_injective
  change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

lemma polar_apply_basis {n : ℕ} (X : RealMatrix n n) (i : Fin n) :
    polarCLM X (singularBasis X i) = leftSingularVector X i := by
  simp [polarCLM, (singularBasis X).inner_eq_ite]

lemma polar_norm_sq {n : ℕ} (X : RealMatrix n n) (x : Euclid n) :
    ‖polarCLM X x‖^2 = ∑ i, (inner ℝ (singularBasis X i) x)^2 *
      (if singularValue X i = 0 then 0 else 1) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [polarCLM, sum_apply, InnerProductSpace.rankOne_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial,
    leftSingularVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite, Finset.sum_ite_eq', pow_two]

lemma polar_contraction {n : ℕ} (X : RealMatrix n n) : spectralNorm (polarMatrix X) ≤ 1 := by
  rw [spectral_eq_norm, matrixCLM_polar]
  apply (polarCLM X).opNorm_le_bound (by norm_num)
  intro x
  have h : ‖polarCLM X x‖^2 ≤ ‖x‖^2 := by
    rw [polar_norm_sq, ← (singularBasis X).sum_sq_norm_inner_right x]
    apply Finset.sum_le_sum
    intro i _
    by_cases hz : singularValue X i = 0
    · rw [if_pos hz, mul_zero]
      exact sq_nonneg _
    · simp [hz, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg x, norm_nonneg (polarCLM X x)]

end RankSparsityProof

open scoped BigOperators Classical
open Matrix MatrixCompletion RankSparsity.Recovery

namespace RankSparsityProof

theorem inner_trace_eq {n : ℕ} (X Y : RealMatrix n n) :
    matrixInner X Y = trace (Xᵀ * Y) := by
  simp only [matrixInner, trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

theorem inner_mul_left {n : ℕ} (P X Y : RealMatrix n n) :
    matrixInner (P * X) Y = matrixInner X (Pᵀ * Y) := by
  simp only [inner_trace_eq, transpose_mul, Matrix.mul_assoc]

theorem inner_mul_right {n : ℕ} (P X Y : RealMatrix n n) :
    matrixInner (X * P) Y = matrixInner X (Y * Pᵀ) := by
  simp only [inner_trace_eq, transpose_mul, Matrix.mul_assoc]
  rw [trace_mul_comm]
  rw [Matrix.mul_assoc]

theorem inner_sub_left {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner (X - Y) Z = matrixInner X Z - matrixInner Y Z := by
  simp only [matrixInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem inner_sub_right {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner X (Y - Z) = matrixInner X Y - matrixInner X Z := by
  simp only [matrixInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem inner_add_left {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner (X + Y) Z = matrixInner X Z + matrixInner Y Z := by
  simp only [matrixInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem inner_add_right {n : ℕ} (X Y Z : RealMatrix n n) :
    matrixInner X (Y + Z) = matrixInner X Y + matrixInner X Z := by
  simp only [matrixInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem inner_smul_left {n : ℕ} (a : ℝ) (X Y : RealMatrix n n) :
    matrixInner (a • X) Y = a * matrixInner X Y := by
  simp only [matrixInner, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem inner_smul_right {n : ℕ} (a : ℝ) (X Y : RealMatrix n n) :
    matrixInner X (a • Y) = a * matrixInner X Y := by
  simp only [matrixInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem inner_comm {n : ℕ} (X Y : RealMatrix n n) : matrixInner X Y = matrixInner Y X := by
  simp only [matrixInner, mul_comm]

theorem inner_zero_left {n : ℕ} (X : RealMatrix n n) : matrixInner 0 X = 0 := by
  simp [matrixInner]

theorem inner_zero_right {n : ℕ} (X : RealMatrix n n) : matrixInner X 0 = 0 := by
  simp [matrixInner]

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

lemma inner_le_spectral_mul_nuclear {n : ℕ} (W X : RealMatrix n n) :
    |matrixInner W X| ≤ spectralNorm W * nuclearNorm X := by
  rw [matrixInner_basis W X (singularBasis X), nuclear_eq_sum_singularValue,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  calc
    |inner ℝ (matrixCLM W (singularBasis X i)) (matrixCLM X (singularBasis X i))| ≤
        ‖matrixCLM W (singularBasis X i)‖ * ‖matrixCLM X (singularBasis X i)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ spectralNorm W * singularValue X i := by
      rw [singular_image_norm]
      apply mul_le_mul_of_nonneg_right _ (singularValue_nonneg X i)
      simpa only [spectral_eq_norm, (singularBasis X).orthonormal.1 i, mul_one] using
        (matrixCLM W).le_opNorm (singularBasis X i)

lemma polar_pairing {n : ℕ} (X : RealMatrix n n) :
    matrixInner (polarMatrix X) X = nuclearNorm X := by
  rw [matrixInner_basis _ _ (singularBasis X), nuclear_eq_sum_singularValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [matrixCLM_polar, polar_apply_basis, singular_image_eq, _root_.inner_smul_right,
    leftSingularVector_inner]
  by_cases h : singularValue X i = 0 <;> simp [h]

lemma polar_attains {n : ℕ} (X : RealMatrix n n) :
    ∃ W : RealMatrix n n, spectralNorm W ≤ 1 ∧ matrixInner W X = nuclearNorm X :=
  ⟨polarMatrix X, polar_contraction X, polar_pairing X⟩

lemma inner_le_nuclear_of_contraction {n : ℕ} (W X : RealMatrix n n)
    (hW : spectralNorm W ≤ 1) : matrixInner W X ≤ nuclearNorm X := by
  calc
    matrixInner W X ≤ |matrixInner W X| := le_abs_self _
    _ ≤ spectralNorm W * nuclearNorm X := inner_le_spectral_mul_nuclear W X
    _ ≤ 1 * nuclearNorm X := mul_le_mul_of_nonneg_right hW (nuclear_nonneg X)
    _ = nuclearNorm X := one_mul _

lemma nuclear_add_le {n : ℕ} (X Y : RealMatrix n n) :
    nuclearNorm (X + Y) ≤ nuclearNorm X + nuclearNorm Y := by
  obtain ⟨W, hW, he⟩ := polar_attains (X+Y)
  rw [← he, inner_add_right]
  exact add_le_add (inner_le_nuclear_of_contraction W X hW)
    (inner_le_nuclear_of_contraction W Y hW)

lemma nuclear_neg {n : ℕ} (X : RealMatrix n n) : nuclearNorm (-X) = nuclearNorm X := by
  have hh : ∀ Y : RealMatrix n n, nuclearNorm (-Y) ≤ nuclearNorm Y := by
    intro Y
    obtain ⟨W, hW, he⟩ := polar_attains (-Y)
    calc
      nuclearNorm (-Y) = -matrixInner W Y := by
        rw [← he]
        simp [matrixInner]
      _ ≤ |matrixInner W Y| := neg_le_abs _
      _ ≤ spectralNorm W * nuclearNorm Y := inner_le_spectral_mul_nuclear W Y
      _ ≤ nuclearNorm Y := by nlinarith [nuclear_nonneg Y]
  exact le_antisymm (hh X) (by simpa using hh (-X))

end RankSparsityProof

open scoped BigOperators Classical Matrix.Norms.Elementwise
open Matrix MatrixCompletion RankSparsity.Recovery WithLp

namespace RankSparsityProof

private theorem pi_norm_ciSup {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    (f : ι → F) : ‖f‖ = ⨆ i, ‖f i‖ :=
  (PiLp.norm_toLp f).symm.trans (PiLp.norm_eq_ciSup (toLp (⊤ : ENNReal) f))

theorem entry_eq_norm {n : ℕ} (X : RealMatrix n n) : entrySupNorm X = ‖X‖ := by
  change (⨆ i, ⨆ j, |X i j|) = ‖(fun i j => X i j)‖
  simp only [← Real.norm_eq_abs, ← pi_norm_ciSup]
  exact (pi_norm_ciSup (fun i => X i)).symm

theorem entry_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ entrySupNorm X := by
  rw [entry_eq_norm]
  exact norm_nonneg _

theorem entry_eq_zero_iff {n : ℕ} (X : RealMatrix n n) :
    entrySupNorm X = 0 ↔ X = 0 := by rw [entry_eq_norm, norm_eq_zero]

theorem entry_zero {n : ℕ} : entrySupNorm (0 : RealMatrix n n) = 0 :=
  (entry_eq_zero_iff _).mpr rfl

theorem entry_add_le {n : ℕ} (X Y : RealMatrix n n) :
    entrySupNorm (X + Y) ≤ entrySupNorm X + entrySupNorm Y := by
  simp only [entry_eq_norm]
  exact norm_add_le _ _

theorem entry_smul {n : ℕ} (a : ℝ) (X : RealMatrix n n) :
    entrySupNorm (a • X) = |a| * entrySupNorm X := by
  simp only [entry_eq_norm, norm_smul, Real.norm_eq_abs]

theorem entry_neg {n : ℕ} (X : RealMatrix n n) : entrySupNorm (-X) = entrySupNorm X := by
  simp only [entry_eq_norm, norm_neg]

theorem entry_le {n : ℕ} {X : RealMatrix n n} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |X i j| ≤ c) : entrySupNorm X ≤ c := by
  rw [entry_eq_norm]
  exact (pi_norm_le_iff_of_nonneg hc).mpr fun i =>
    (pi_norm_le_iff_of_nonneg hc).mpr fun j => by simpa only [Real.norm_eq_abs] using h i j

theorem abs_entry_le {n : ℕ} (X : RealMatrix n n) (i j : Fin n) :
    |X i j| ≤ entrySupNorm X := by
  rw [entry_eq_norm, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm (X i) j).trans (norm_le_pi_norm X i)

theorem omega_iff {n : ℕ} (A X : RealMatrix n n) :
    InOmega A X ↔ ∀ i j, A i j = 0 → X i j = 0 := by
  simp only [InOmega, supp, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.forall]
  constructor
  · intro h i j ha
    by_contra hx
    exact h i j hx ha
  · intro h i j hx ha
    exact hx (h i j ha)

noncomputable def supportSpace {n : ℕ} (A : RealMatrix n n) : Submodule ℝ (RealMatrix n n) where
  carrier := {X | InOmega A X}
  zero_mem' := (omega_iff A 0).mpr (by intros; rfl)
  add_mem' := by
    intro X Y hX hY
    exact (omega_iff A _).mpr fun i j ha => by
      simp only [Matrix.add_apply, (omega_iff A X).mp hX i j ha,
        (omega_iff A Y).mp hY i j ha, add_zero]
  smul_mem' := by
    intro a X hX
    exact (omega_iff A _).mpr fun i j ha => by
      simp only [Matrix.smul_apply, smul_eq_mul, (omega_iff A X).mp hX i j ha, mul_zero]

theorem omega_smul {n : ℕ} {A X : RealMatrix n n} (hX : InOmega A X) (a : ℝ) :
    InOmega A (a • X) := (supportSpace A).smul_mem a hX

theorem omega_zero {n : ℕ} (A : RealMatrix n n) : InOmega A 0 :=
  (supportSpace A).zero_mem

theorem omega_self {n : ℕ} (A : RealMatrix n n) : InOmega A A := Finset.Subset.refl _

theorem omega_apply {n : ℕ} (A X : RealMatrix n n) (i j : Fin n) :
    projOmega A X i j = if A i j ≠ 0 then X i j else 0 := by
  simp only [projOmega, samplingProjection, supp, Finset.mem_filter, Finset.mem_univ, true_and]

theorem omegaC_apply {n : ℕ} (A X : RealMatrix n n) (i j : Fin n) :
    projOmegaC A X i j = if A i j = 0 then X i j else 0 := by
  change X i j - projOmega A X i j = _
  rw [omega_apply]
  split_ifs <;> simp_all

theorem omega_mem {n : ℕ} (A X : RealMatrix n n) : InOmega A (projOmega A X) :=
  (omega_iff A _).mpr fun i j ha => by simp [omega_apply, ha]

theorem omega_eq_self {n : ℕ} {A X : RealMatrix n n} (hX : InOmega A X) :
    projOmega A X = X := by
  ext i j
  rw [omega_apply]
  split_ifs with h
  · rfl
  · exact ((omega_iff A X).mp hX i j (not_not.mp h)).symm

theorem omegaC_eq_zero_iff {n : ℕ} (A X : RealMatrix n n) :
    projOmegaC A X = 0 ↔ InOmega A X := by
  change X - projOmega A X = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    rw [h]
    exact omega_mem _ _
  · exact fun h => (omega_eq_self h).symm

theorem omega_add {n : ℕ} (A X Y : RealMatrix n n) :
    projOmega A (X + Y) = projOmega A X + projOmega A Y := by
  ext i j
  simp only [omega_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem omega_smul_map {n : ℕ} (A X : RealMatrix n n) (a : ℝ) :
    projOmega A (a • X) = a • projOmega A X := by
  ext i j
  simp only [omega_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem omega_entry_le {n : ℕ} (A X : RealMatrix n n) :
    entrySupNorm (projOmega A X) ≤ entrySupNorm X := by
  apply entry_le (entry_nonneg X)
  intro i j
  rw [omega_apply]
  split_ifs
  · exact abs_entry_le _ _ _
  · simpa using entry_nonneg X

theorem omegaC_entry_le {n : ℕ} (A X : RealMatrix n n) :
    entrySupNorm (projOmegaC A X) ≤ entrySupNorm X := by
  apply entry_le (entry_nonneg X)
  intro i j
  rw [omegaC_apply]
  split_ifs
  · exact abs_entry_le _ _ _
  · simpa using entry_nonneg X

theorem omega_inner {n : ℕ} (A X Y : RealMatrix n n) :
    matrixInner (projOmega A X) Y = matrixInner X (projOmega A Y) := by
  unfold matrixInner
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [omega_apply]
  split_ifs <;> simp

theorem omegaC_inner {n : ℕ} (A X Y : RealMatrix n n) :
    matrixInner (projOmegaC A X) Y = matrixInner X (projOmegaC A Y) := by
  unfold matrixInner
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [omegaC_apply]
  split_ifs <;> simp

theorem sign_omega {n : ℕ} (A : RealMatrix n n) : InOmega A (entrySign A) :=
  (omega_iff A _).mpr fun i j ha => by simp [entrySign, ha]

theorem sign_entry_le {n : ℕ} (A : RealMatrix n n) : entrySupNorm (entrySign A) ≤ 1 := by
  apply entry_le zero_le_one
  intro i j
  simp only [entrySign]
  rcases lt_trichotomy (A i j) 0 with h | h | h
  · simp [Real.sign_of_neg h]
  · simp [h]
  · simp [Real.sign_of_pos h]

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

lemma l1_nonneg {n : ℕ} (X : RealMatrix n n) : 0 ≤ l1Norm X := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (X i j)

lemma l1_eq_zero_iff {n : ℕ} (X : RealMatrix n n) : l1Norm X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg (X i j))).mp h
    ext i j
    have hi := h' i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (X i j))).mp hi j
      (Finset.mem_univ j)
    exact abs_eq_zero.mp hj
  · rintro rfl
    simp [l1Norm]

lemma entry_inner_bound {n : ℕ} (W X : RealMatrix n n) :
    |matrixInner W X| ≤ entrySupNorm W * l1Norm X := by
  unfold matrixInner l1Norm
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_entry_le W i j) (abs_nonneg _)

lemma l1_support_gap {n : ℕ} (A H : RealMatrix n n) :
    l1Norm A - matrixInner (entrySign A) H + l1Norm (projOmegaC A H) ≤ l1Norm (A-H) := by
  simp only [l1Norm, matrixInner, entrySign, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [omegaC_apply]
  change |A i j| - Real.sign (A i j) * H i j +
    |if A i j = 0 then H i j else 0| ≤ |A i j - H i j|
  by_cases h : A i j = 0
  · simp [h]
  · rcases lt_or_gt_of_ne h with hn | hp
    · rw [Real.sign_of_neg hn, abs_of_neg hn, if_neg h]
      have ht := neg_le_abs (A i j - H i j)
      simpa [add_comm] using ht
    · rw [Real.sign_of_pos hp, abs_of_pos hp, if_neg h]
      simpa using le_abs_self (A i j - H i j)

end RankSparsityProof

open scoped BigOperators Classical
open Matrix MatrixCompletion RankSparsity.Recovery

namespace RankSparsityProof

noncomputable def familyProj {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  ∑ k, vecMulVec (u k) (u k)

noncomputable def uProjector {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) := familyProj S.u
noncomputable def vProjector {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) := familyProj S.v

theorem familyProj_apply {n r : ℕ} (u : Fin r → Fin n → ℝ) (i j : Fin n) :
    familyProj u i j = ∑ k, u k i * u k j := by
  simp only [familyProj, Matrix.sum_apply, vecMulVec_apply]

theorem familyProj_transpose {n r : ℕ} (u : Fin r → Fin n → ℝ) :
    (familyProj u)ᵀ = familyProj u := by
  ext i j
  simp only [transpose_apply, familyProj_apply, mul_comm]

theorem familyProj_idem {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) :
    familyProj u * familyProj u = familyProj u := by
  simp only [familyProj, Finset.sum_mul, Finset.mul_sum, vecMulVec_mul_vecMulVec,
    dotProduct, hu, vecMulVec_smul]
  simp

theorem familyProj_fix {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (l : Fin r) :
    familyProj u *ᵥ u l = u l := by
  rw [familyProj, sum_mulVec]
  ext i
  simp only [Finset.sum_apply, vecMulVec_mulVec, dotProduct, hu]
  simp

theorem u_transpose {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    (uProjector S)ᵀ = uProjector S := familyProj_transpose _
theorem v_transpose {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    (vProjector S)ᵀ = vProjector S := familyProj_transpose _
theorem u_idem {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    uProjector S * uProjector S = uProjector S := familyProj_idem _ S.u_orthonormal
theorem v_idem {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    vProjector S * vProjector S = vProjector S := familyProj_idem _ S.v_orthonormal

theorem left_eq_mul {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    leftSingularProjection S X = uProjector S * X := by
  ext i j
  simp only [leftSingularProjection, mul_apply, uProjector, familyProj_apply]

theorem right_eq_mul {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    rightSingularProjection S X = X * vProjector S := by
  ext i j
  simp only [rightSingularProjection, mul_apply, vProjector, familyProj_apply]

theorem two_eq_mul {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    twoSidedSingularProjection S X = uProjector S * X * vProjector S := by
  ext i j
  simp only [twoSidedSingularProjection, mul_apply, uProjector, vProjector,
    familyProj_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem tangent_formula {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    tangentProjection S X = uProjector S * X + X * vProjector S -
      uProjector S * X * vProjector S := by
  simp only [tangentProjection, left_eq_mul, right_eq_mul, two_eq_mul]

theorem tangent_formula' {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    tangentProjection S X = uProjector S * X + (1 - uProjector S) * X * vProjector S := by
  rw [tangent_formula]
  simp only [sub_mul, one_mul]
  abel

theorem normal_formula {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    normalProjection S X = (1 - uProjector S) * X * (1 - vProjector S) := by
  rw [normalProjection, tangent_formula]
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  abel

theorem normal_inner {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X Y : RealMatrix n n) :
    matrixInner (normalProjection S X) Y = matrixInner X (normalProjection S Y) := by
  rw [normal_formula, normal_formula, inner_mul_right, inner_mul_left]
  simp only [transpose_sub, transpose_one, u_transpose, v_transpose, Matrix.mul_assoc]

theorem tangent_inner {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X Y : RealMatrix n n) :
    matrixInner (tangentProjection S X) Y = matrixInner X (tangentProjection S Y) := by
  have h := normal_inner S X Y
  simp only [normalProjection, inner_sub_left, inner_sub_right] at h
  linarith

theorem tangent_add {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X Y : RealMatrix n n) :
    tangentProjection S (X + Y) = tangentProjection S X + tangentProjection S Y := by
  simp only [tangent_formula, mul_add, add_mul]
  abel

theorem tangent_smul {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (a : ℝ) (X : RealMatrix n n) :
    tangentProjection S (a • X) = a • tangentProjection S X := by
  simp only [tangent_formula, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub]

theorem tangent_zero {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    tangentProjection S 0 = 0 := by simp [tangent_formula]

theorem tangent_sub {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X Y : RealMatrix n n) :
    tangentProjection S (X - Y) = tangentProjection S X - tangentProjection S Y := by
  simp only [tangent_formula, mul_sub, sub_mul]
  abel

theorem normal_add {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X Y : RealMatrix n n) :
    normalProjection S (X + Y) = normalProjection S X + normalProjection S Y := by
  simp only [normal_formula, mul_add, add_mul]

theorem normal_idem {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    normalProjection S (normalProjection S X) = normalProjection S X := by
  have hu : (1 - uProjector S) * (1 - uProjector S) = 1 - uProjector S := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, u_idem]
    abel
  have hv : (1 - vProjector S) * (1 - vProjector S) = 1 - vProjector S := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, v_idem]
    abel
  simp only [normal_formula]
  calc
    _ = ((1 - uProjector S) * (1 - uProjector S)) * X *
        ((1 - vProjector S) * (1 - vProjector S)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, hv]

theorem tangent_idem {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  have h := normal_idem S X
  simp only [normalProjection, tangent_sub] at h
  exact (sub_eq_zero.mp (sub_eq_self.mp h)).symm

end RankSparsityProof

open scoped BigOperators Classical
open Matrix MatrixCompletion RankSparsity.Recovery WithLp

namespace RankSparsityProof

theorem symmetric_idem_spectral_le {n : ℕ} (P : RealMatrix n n)
    (ht : Pᵀ = P) (hi : P * P = P) : spectralNorm P ≤ 1 := by
  have hs : (Matrix.toEuclideanLin P).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (by simpa [Matrix.IsHermitian] using ht)
  rw [spectral_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hid : matrixCLM P (matrixCLM P v) = matrixCLM P v := by
    rw [← ContinuousLinearMap.comp_apply, ← matrixCLM_mul, hi]
  have hp : ‖matrixCLM P v‖ ^ 2 ≤ ‖v‖ * ‖matrixCLM P v‖ := by
    calc
      _ = inner ℝ (matrixCLM P v) (matrixCLM P v) := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ v (matrixCLM P (matrixCLM P v)) := hs _ _
      _ = inner ℝ v (matrixCLM P v) := by rw [hid]
      _ ≤ _ := real_inner_le_norm _ _
  have hn := norm_nonneg (matrixCLM P v)
  have hv := norm_nonneg v
  simp only [one_mul]
  nlinarith

theorem u_spectral_le {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    spectralNorm (uProjector S) ≤ 1 := symmetric_idem_spectral_le _ (u_transpose S) (u_idem S)
theorem v_spectral_le {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    spectralNorm (vProjector S) ≤ 1 := symmetric_idem_spectral_le _ (v_transpose S) (v_idem S)

theorem complement_spectral_le {n : ℕ} (P : RealMatrix n n)
    (ht : Pᵀ = P) (hi : P * P = P) : spectralNorm (1 - P) ≤ 1 := by
  apply symmetric_idem_spectral_le
  · simp only [transpose_sub, transpose_one, ht]
  · simp only [sub_mul, mul_sub, one_mul, mul_one, hi]
    abel

theorem normal_spectral_le {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    spectralNorm (normalProjection S X) ≤ spectralNorm X := by
  rw [normal_formula]
  have hu := complement_spectral_le _ (u_transpose S) (u_idem S)
  have hv := complement_spectral_le _ (v_transpose S) (v_idem S)
  calc
    _ ≤ spectralNorm ((1 - uProjector S) * X) * spectralNorm (1 - vProjector S) := spectral_mul_le _ _
    _ ≤ spectralNorm ((1 - uProjector S) * X) * 1 :=
      mul_le_mul_of_nonneg_left hv (spectral_nonneg _)
    _ ≤ spectralNorm X := by
      rw [mul_one]
      exact (spectral_mul_le _ _).trans (by nlinarith [spectral_nonneg X])

theorem tangent_spectral_le {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    spectralNorm (tangentProjection S X) ≤ 2 * spectralNorm X := by
  have h1 : spectralNorm (uProjector S * X) ≤ spectralNorm X :=
    (spectral_mul_le _ _).trans (by nlinarith [u_spectral_le S, spectral_nonneg X])
  have h2 : spectralNorm ((1 - uProjector S) * X * vProjector S) ≤ spectralNorm X := by
    have hu := complement_spectral_le _ (u_transpose S) (u_idem S)
    have hleft : spectralNorm ((1 - uProjector S) * X) ≤ spectralNorm X :=
      (spectral_mul_le _ _).trans (by nlinarith [spectral_nonneg X])
    exact (spectral_mul_le _ _).trans (by nlinarith [v_spectral_le S, spectral_nonneg ((1 - uProjector S) * X)])
  rw [tangent_formula']
  exact (spectral_add_le _ _).trans (by linarith)

theorem inT_tangent {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    InT S (tangentProjection S X) := by
  rw [tangent_formula']
  refine ⟨fun k => (S.u k) ᵥ* X, fun k => ((1 - uProjector S) * X) *ᵥ S.v k, ?_⟩
  simp only [uProjector, vProjector, familyProj, Finset.sum_mul, Finset.mul_sum,
    vecMulVec_mul, mul_vecMulVec]

theorem inT_iff_tangent_eq {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    InT S X ↔ tangentProjection S X = X := by
  constructor
  · rintro ⟨a, b, rfl⟩
    have hu : uProjector S * (∑ k, vecMulVec (S.u k) (a k)) = ∑ k, vecMulVec (S.u k) (a k) := by
      simp only [Finset.mul_sum, mul_vecMulVec, uProjector,
        familyProj_fix _ S.u_orthonormal]
    have hv : (∑ k, vecMulVec (b k) (S.v k)) * vProjector S = ∑ k, vecMulVec (b k) (S.v k) := by
      simp only [Finset.sum_mul, vecMulVec_mul]
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      rw [← v_transpose S, vecMul_transpose]
      exact familyProj_fix _ S.v_orthonormal k
    rw [tangent_formula]
    simp only [mul_add, add_mul, hu, hv, Matrix.mul_assoc]
    abel
  · intro h
    rw [← h]
    exact inT_tangent S X

theorem normal_eq_zero_iff_inT {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (X : RealMatrix n n) :
    normalProjection S X = 0 ↔ InT S X := by
  rw [normalProjection, sub_eq_zero, inT_iff_tangent_eq, eq_comm]

theorem inT_smul {n r : ℕ} {B : RealMatrix n n} {S : SVD B r} {X : RealMatrix n n}
    (hX : InT S X) (a : ℝ) : InT S (a • X) := by
  rw [inT_iff_tangent_eq] at hX ⊢
  rw [tangent_smul, hX]

theorem inT_zero {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) : InT S 0 := by
  rw [inT_iff_tangent_eq, tangent_zero]

theorem sign_inT {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) : InT S (signMatrix S) := by
  refine ⟨S.v, fun _ => 0, ?_⟩
  simp [signMatrix]

theorem svd_inT {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) : InT S B := by
  refine ⟨fun k => S.sigma k • S.v k, fun _ => 0, ?_⟩
  simp only [zero_vecMulVec, Finset.sum_const_zero, add_zero, vecMulVec_smul]
  exact S.decomp

end RankSparsityProof

open Matrix MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

lemma sign_transpose_mul {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    (signMatrix S)ᵀ * signMatrix S = vProjector S := by
  simp only [signMatrix, transpose_sum, transpose_vecMulVec, Finset.sum_mul,
    Finset.mul_sum, vecMulVec_mul_vecMulVec, dotProduct, S.u_orthonormal, vecMulVec_smul]
  simp [vProjector, familyProj]

lemma u_mul_sign {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    uProjector S * signMatrix S = signMatrix S := by
  simp only [uProjector, familyProj, signMatrix, Finset.sum_mul,
    Finset.mul_sum, vecMulVec_mul_vecMulVec, dotProduct, S.u_orthonormal, vecMulVec_smul]
  simp

lemma sign_mul_v {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    signMatrix S * vProjector S = signMatrix S := by
  simp only [vProjector, familyProj, signMatrix, Finset.sum_mul,
    Finset.mul_sum, vecMulVec_mul_vecMulVec, dotProduct, S.v_orthonormal, vecMulVec_smul]
  simp

lemma matrixCLM_inner_transpose {n : ℕ} (X : RealMatrix n n) (u v : Euclid n) :
    inner ℝ (matrixCLM X u) v = inner ℝ u (matrixCLM Xᵀ v) := by
  have ht : Matrix.toEuclideanLin Xᵀ = (Matrix.toEuclideanLin X).adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint X
  change inner ℝ (Matrix.toEuclideanLin X u) v = inner ℝ u (Matrix.toEuclideanLin Xᵀ v)
  rw [ht, LinearMap.adjoint_inner_right]

lemma projector_norm_sq {n : ℕ} (P : RealMatrix n n) (ht : Pᵀ=P) (hi : P*P=P)
    (x : Euclid n) : ‖matrixCLM P x‖^2 = inner ℝ x (matrixCLM P x) := by
  rw [← real_inner_self_eq_norm_sq, matrixCLM_inner_transpose, ht]
  rw [← ContinuousLinearMap.comp_apply, ← matrixCLM_mul, hi]

lemma projector_pythagoras {n : ℕ} (P : RealMatrix n n) (ht : Pᵀ=P) (hi : P*P=P)
    (x : Euclid n) : ‖matrixCLM P x‖^2 + ‖matrixCLM (1-P) x‖^2 = ‖x‖^2 := by
  have he : matrixCLM (1-P) x = x - matrixCLM P x := by
    change Matrix.toEuclideanLin (1-P) x = _
    rw [map_sub]
    simp [Matrix.toEuclideanLin, matrixCLM]
  rw [he, norm_sub_sq_real, projector_norm_sq P ht hi]
  ring

lemma sign_norm_sq {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (x : Euclid n) :
    ‖matrixCLM (signMatrix S) x‖^2 = ‖matrixCLM (vProjector S) x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, matrixCLM_inner_transpose,
    ← ContinuousLinearMap.comp_apply, ← matrixCLM_mul, sign_transpose_mul,
    projector_norm_sq _ (v_transpose S) (v_idem S)]

lemma sign_spectral_le {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    spectralNorm (signMatrix S) ≤ 1 := by
  rw [spectral_eq_norm]
  apply (matrixCLM (signMatrix S)).opNorm_le_bound zero_le_one
  intro x
  have he := sign_norm_sq S x
  have hb := (matrixCLM (vProjector S)).le_opNorm x
  have hn := v_spectral_le S
  rw [spectral_eq_norm] at hn
  have hz := norm_nonneg x
  have hp := norm_nonneg (matrixCLM (vProjector S) x)
  have hs := norm_nonneg (matrixCLM (signMatrix S) x)
  have hc : ‖matrixCLM (vProjector S) x‖ ≤ ‖x‖ := by nlinarith
  nlinarith

lemma sign_add_normal_contraction {n r : ℕ} {B : RealMatrix n n} (S : SVD B r)
    (W : RealMatrix n n) (hW : spectralNorm W ≤ 1) :
    spectralNorm (signMatrix S + normalProjection S W) ≤ 1 := by
  have hcross : (signMatrix S)ᵀ * normalProjection S W = 0 := by
    have hu := congrArg Matrix.transpose (u_mul_sign S)
    simp only [transpose_mul, u_transpose] at hu
    have hz : (signMatrix S)ᵀ * (1-uProjector S) = 0 := by
      rw [mul_sub, mul_one, hu, sub_self]
    rw [normal_formula]
    calc
      _ = ((signMatrix S)ᵀ * (1-uProjector S)) * W * (1-vProjector S) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hz, zero_mul, zero_mul]
  rw [spectral_eq_norm]
  apply (matrixCLM _).opNorm_le_bound zero_le_one
  intro x
  have ho : inner ℝ (matrixCLM (signMatrix S) x) (matrixCLM (normalProjection S W) x) = 0 := by
    rw [matrixCLM_inner_transpose, ← ContinuousLinearMap.comp_apply, ← matrixCLM_mul,
      hcross, matrixCLM_zero]
    simp
  have hb : ‖matrixCLM (normalProjection S W) x‖ ≤ ‖matrixCLM (1-vProjector S) x‖ := by
    rw [normal_formula, matrixCLM_mul, matrixCLM_mul]
    simp only [ContinuousLinearMap.comp_apply]
    have hU := complement_spectral_le _ (u_transpose S) (u_idem S)
    rw [spectral_eq_norm] at hU hW
    exact ((matrixCLM (1-uProjector S)).le_opNorm _).trans (by
      have hw := (matrixCLM W).le_opNorm (matrixCLM (1-vProjector S) x)
      nlinarith [norm_nonneg (matrixCLM W (matrixCLM (1-vProjector S) x)),
        norm_nonneg (matrixCLM (1-vProjector S) x)])
  have hp := projector_pythagoras _ (v_transpose S) (v_idem S) x
  have hs := sign_norm_sq S x
  have he := norm_add_sq_real (matrixCLM (signMatrix S) x) (matrixCLM (normalProjection S W) x)
  rw [ho] at he
  rw [matrixCLM_add, _root_.add_apply]
  nlinarith [norm_nonneg x, norm_nonneg (matrixCLM (normalProjection S W) x),
    norm_nonneg (matrixCLM (1-vProjector S) x),
    norm_nonneg (matrixCLM (signMatrix S) x + matrixCLM (normalProjection S W) x)]

end RankSparsityProof

open Matrix MatrixCompletion RankSparsity.Recovery WithLp
open scoped BigOperators Classical

namespace RankSparsityProof

lemma svd_u_orthonormal {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    Orthonormal ℝ (fun k => toLp 2 (S.u k)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using S.u_orthonormal i j

lemma svd_v_orthonormal {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    Orthonormal ℝ (fun k => toLp 2 (S.v k)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using S.v_orthonormal i j

lemma inner_vecMulVec {n : ℕ} (W : RealMatrix n n) (u v : Fin n → ℝ) :
    matrixInner W (vecMulVec u v) = inner ℝ (toLp 2 u) (matrixCLM W (toLp 2 v)) := by
  change (∑ i, ∑ j, W i j * (u i * v j)) = ∑ i, (∑ j, W i j * v j) * u i
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sign_apply_v {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (k : Fin r) :
    matrixCLM (signMatrix S) (toLp 2 (S.v k)) = toLp 2 (S.u k) := by
  ext i
  change (signMatrix S *ᵥ S.v k) i = S.u k i
  simp only [signMatrix, sum_mulVec, vecMulVec_mulVec, dotProduct, S.v_orthonormal]
  simp [ite_apply]

lemma inner_svd_decomp {n r : ℕ} {B : RealMatrix n n} (S : SVD B r)
    (W : RealMatrix n n) : matrixInner W B =
      ∑ k, S.sigma k * inner ℝ (toLp 2 (S.u k)) (matrixCLM W (toLp 2 (S.v k))) := by
  have hsum (Z : Fin r → RealMatrix n n) : matrixInner W (∑ k, Z k) =
      ∑ k, matrixInner W (Z k) := by
    simp only [matrixInner, Matrix.sum_apply, Finset.mul_sum]
    calc
      _ = ∑ i, ∑ k, ∑ j, W i j * Z k i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  conv_lhs => rw [S.decomp]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k _
  rw [inner_smul_right, inner_vecMulVec]

lemma sign_pairing {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    matrixInner (signMatrix S) B = nuclearNorm B := by
  have he : matrixInner (signMatrix S) B = ∑ k, S.sigma k := by
    rw [inner_svd_decomp S]
    simp only [sign_apply_v, real_inner_self_eq_norm_sq, (svd_u_orthonormal S).1,
      one_pow, mul_one]
  have hu : nuclearNorm B ≤ ∑ k, S.sigma k := by
    obtain ⟨W,hW,hB⟩ := polar_attains B
    rw [← hB, inner_svd_decomp S]
    apply Finset.sum_le_sum
    intro k _
    have hb := (matrixCLM W).le_opNorm (toLp 2 (S.v k))
    have hi := real_inner_le_norm (toLp 2 (S.u k)) (matrixCLM W (toLp 2 (S.v k)))
    rw [(svd_u_orthonormal S).1 k, one_mul] at hi
    rw [(svd_v_orthonormal S).1 k, mul_one] at hb
    rw [spectral_eq_norm] at hW
    have hi1 : inner ℝ (toLp 2 (S.u k)) (matrixCLM W (toLp 2 (S.v k))) ≤ 1 :=
      hi.trans (hb.trans hW)
    nlinarith [S.sigma_pos k]
  exact le_antisymm (inner_le_nuclear_of_contraction _ _ (sign_spectral_le S)) (by rw [he]; exact hu)

lemma nuclear_normal_gap {n r : ℕ} {B : RealMatrix n n} (S : SVD B r)
    (H : RealMatrix n n) : nuclearNorm B + matrixInner (signMatrix S) H +
      nuclearNorm (normalProjection S H) ≤ nuclearNorm (B+H) := by
  obtain ⟨W,hW,hH⟩ := polar_attains (normalProjection S H)
  have hb : normalProjection S B = 0 := (normal_eq_zero_iff_inT S B).mpr (svd_inT S)
  have h := inner_le_nuclear_of_contraction (signMatrix S + normalProjection S W) (B+H)
    (sign_add_normal_contraction S W hW)
  rw [inner_add_left, inner_add_right, inner_add_right, sign_pairing,
    normal_inner, normal_inner, hb, inner_zero_right, hH] at h
  linarith

end RankSparsityProof

open scoped BigOperators Classical Matrix.Norms.Elementwise
open Matrix MatrixCompletion RankSparsity.Recovery

namespace RankSparsityProof

theorem finite_norm_bounds {n : ℕ} : ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧
    (∀ X : RealMatrix n n, spectralNorm X ≤ c * entrySupNorm X) ∧
    (∀ X : RealMatrix n n, entrySupNorm X ≤ d * spectralNorm X) := by
  let e : (Fin n → Fin n → ℝ) ≃ₗ[ℝ] (Euclid n →L[ℝ] Euclid n) :=
    (Matrix.toEuclideanLin).trans LinearMap.toContinuousLinearMap
  let f : (Fin n → Fin n → ℝ) →L[ℝ] (Euclid n →L[ℝ] Euclid n) :=
    LinearMap.toContinuousLinearMap e.toLinearMap
  let g : (Euclid n →L[ℝ] Euclid n) →L[ℝ] (Fin n → Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap e.symm.toLinearMap
  refine ⟨‖f‖, ‖g‖, f.opNorm_nonneg, g.opNorm_nonneg, ?_, ?_⟩
  · intro X
    rw [entry_eq_norm, spectral_eq_norm]
    convert! f.le_opNorm X
  · intro X
    have h := g.le_opNorm (e (fun i j => X i j))
    change ‖e.symm (e (fun i j => X i j))‖ ≤ ‖g‖ * ‖e (fun i j => X i j)‖ at h
    rw [LinearEquiv.symm_apply_apply] at h
    rw [entry_eq_norm, spectral_eq_norm]
    convert! h

theorem mu_bdd {n : ℕ} (A : RealMatrix n n) :
    BddAbove (spectralNorm '' {X : RealMatrix n n | InOmega A X ∧ entrySupNorm X ≤ 1}) := by
  obtain ⟨c, d, hc, _, hb, _⟩ := finite_norm_bounds (n := n)
  refine ⟨c, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact (hb X).trans (by nlinarith [hX.2])

theorem xi_bdd {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) :
    BddAbove (entrySupNorm '' {X : RealMatrix n n | InT S X ∧ spectralNorm X ≤ 1}) := by
  obtain ⟨c, d, _, hd, _, hb⟩ := finite_norm_bounds (n := n)
  refine ⟨d, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact (hb X).trans (by nlinarith [hX.2])

theorem mu_nonneg {n : ℕ} (A : RealMatrix n n) : 0 ≤ mu A := by
  apply le_csSup (mu_bdd A)
  refine ⟨0, ⟨omega_zero A, ?_⟩, ?_⟩
  · rw [entry_zero]
    exact zero_le_one
  · exact (spectral_eq_zero_iff _).mpr rfl

theorem xi_nonneg {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) : 0 ≤ xi S := by
  apply le_csSup (xi_bdd S)
  refine ⟨0, ⟨inT_zero S, ?_⟩, entry_zero⟩
  rw [(spectral_eq_zero_iff _).mpr rfl]
  exact zero_le_one

theorem support_spectral_le {n : ℕ} {A X : RealMatrix n n} (hX : InOmega A X) :
    spectralNorm X ≤ mu A * entrySupNorm X := by
  by_cases hz : X = 0
  · subst X
    rw [(spectral_eq_zero_iff _).mpr rfl, entry_zero, mul_zero]
  have he : 0 < entrySupNorm X := lt_of_le_of_ne (entry_nonneg X) (by
    intro h
    exact hz ((entry_eq_zero_iff X).mp h.symm))
  have hm : spectralNorm ((entrySupNorm X)⁻¹ • X) ≤ mu A := by
    apply le_csSup (mu_bdd A)
    refine ⟨_, ⟨omega_smul hX _, ?_⟩, rfl⟩
    rw [entry_smul, abs_of_pos (inv_pos.mpr he), inv_mul_cancel₀ he.ne']
  rw [spectral_smul, abs_of_pos (inv_pos.mpr he)] at hm
  have hd : spectralNorm X / entrySupNorm X ≤ mu A := by
    simpa only [div_eq_mul_inv, mul_comm] using hm
  exact (div_le_iff₀ he).mp hd

theorem tangent_entry_le {n r : ℕ} {B : RealMatrix n n} {S : SVD B r} {X : RealMatrix n n}
    (hX : InT S X) : entrySupNorm X ≤ xi S * spectralNorm X := by
  by_cases hz : X = 0
  · subst X
    rw [(spectral_eq_zero_iff _).mpr rfl, entry_zero, mul_zero]
  have he : 0 < spectralNorm X := lt_of_le_of_ne (spectral_nonneg X) (by
    intro h
    exact hz ((spectral_eq_zero_iff X).mp h.symm))
  have hm : entrySupNorm ((spectralNorm X)⁻¹ • X) ≤ xi S := by
    apply le_csSup (xi_bdd S)
    refine ⟨_, ⟨inT_smul hX _, ?_⟩, rfl⟩
    rw [spectral_smul, abs_of_pos (inv_pos.mpr he), inv_mul_cancel₀ he.ne']
  rw [entry_smul, abs_of_pos (inv_pos.mpr he)] at hm
  have hd : entrySupNorm X / spectralNorm X ≤ xi S := by
    simpa only [div_eq_mul_inv, mul_comm] using hm
  exact (div_le_iff₀ he).mp hd

theorem mu_pos {n : ℕ} {A : RealMatrix n n} (hA : A ≠ 0) : 0 < mu A := by
  have hs : 0 < spectralNorm A := lt_of_le_of_ne (spectral_nonneg A) (by
    intro h
    exact hA ((spectral_eq_zero_iff A).mp h.symm))
  have h := support_spectral_le (omega_self A)
  nlinarith [mu_nonneg A, entry_nonneg A]

theorem xi_pos {n r : ℕ} {B : RealMatrix n n} (S : SVD B r) (hB : B ≠ 0) : 0 < xi S := by
  have he : 0 < entrySupNorm B := lt_of_le_of_ne (entry_nonneg B) (by
    intro h
    exact hB ((entry_eq_zero_iff B).mp h.symm))
  have h := tangent_entry_le (svd_inT S)
  nlinarith [xi_nonneg S, spectral_nonneg B]

theorem support_tangent_zero {n r : ℕ} (A : RealMatrix n n) {B : RealMatrix n n}
    (S : SVD B r) (h : mu A * xi S < 1) (X : RealMatrix n n)
    (ho : InOmega A X) (ht : InT S X) : X = 0 := by
  have h1 := tangent_entry_le ht
  have h2 := mul_le_mul_of_nonneg_left (support_spectral_le ho) (xi_nonneg S)
  have he : entrySupNorm X = 0 := by
    nlinarith [entry_nonneg X]
  exact (entry_eq_zero_iff X).mp he

end RankSparsityProof

open scoped BigOperators Classical Matrix.Norms.Elementwise
open Matrix MatrixCompletion RankSparsity.Recovery

namespace RankSparsityProof

theorem parameter_pos {n r : ℕ} (A : RealMatrix n n) {B : RealMatrix n n}
    (S : SVD B r) (h : mu A * xi S < 1 / 6) {γ : ℝ}
    (hl : xi S / (1 - 4 * mu A * xi S) < γ) : 0 < γ := by
  have hd : 0 < 1 - 4 * mu A * xi S := by nlinarith
  exact (div_nonneg (xi_nonneg S) hd.le).trans_lt hl

theorem omega_sub_map {n : ℕ} (A X Y : RealMatrix n n) :
    projOmega A (X - Y) = projOmega A X - projOmega A Y := by
  ext i j
  simp only [omega_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem certificate {n r : ℕ} (A : RealMatrix n n) {B : RealMatrix n n}
    (S : SVD B r) (h : mu A * xi S < 1 / 6) (γ : ℝ)
    (hl : xi S / (1 - 4 * mu A * xi S) < γ)
    (hu : γ * mu A < 1 - 3 * mu A * xi S) :
    ∃ Q : RealMatrix n n, projOmega A Q = γ • entrySign A ∧
      tangentProjection S Q = signMatrix S ∧
      spectralNorm (normalProjection S Q) < 1 ∧
      entrySupNorm (projOmegaC A Q) < γ := by
  have ha := mu_nonneg A
  have hb := xi_nonneg S
  have hg := parameter_pos A S h hl
  have hd : 0 < 1 - 2 * mu A * xi S := by nlinarith
  have hd4 : 0 < 1 - 4 * mu A * xi S := by nlinarith
  have hl' := (div_lt_iff₀ hd4).mp hl
  let L : supportSpace A →ₗ[ℝ] supportSpace A :=
    { toFun := fun E => ⟨E.1 - projOmega A (tangentProjection S E.1),
        (supportSpace A).sub_mem E.2 (omega_mem _ _)⟩
      map_add' := by
        intro E F
        apply Subtype.ext
        change (E.1 + F.1) - projOmega A (tangentProjection S (E.1 + F.1)) = _
        rw [tangent_add, omega_add]
        change _ = (E.1 - projOmega A (tangentProjection S E.1)) +
          (F.1 - projOmega A (tangentProjection S F.1))
        abel
      map_smul' := by
        intro a E
        apply Subtype.ext
        change a • E.1 - projOmega A (tangentProjection S (a • E.1)) = _
        rw [tangent_smul, omega_smul_map]
        exact (smul_sub a _ _).symm }
  have hL : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro E hE
    have he : E.1 = projOmega A (tangentProjection S E.1) := by
      have he := congrArg Subtype.val hE
      change E.1 - projOmega A (tangentProjection S E.1) = 0 at he
      exact sub_eq_zero.mp he
    have hbound : entrySupNorm E.1 ≤ 2 * mu A * xi S * entrySupNorm E.1 := by
      calc
        _ = entrySupNorm (projOmega A (tangentProjection S E.1)) := congrArg entrySupNorm he
        _ ≤ entrySupNorm (tangentProjection S E.1) := omega_entry_le _ _
        _ ≤ xi S * spectralNorm (tangentProjection S E.1) := tangent_entry_le (inT_tangent S _)
        _ ≤ xi S * (2 * spectralNorm E.1) := mul_le_mul_of_nonneg_left (tangent_spectral_le _ _) hb
        _ ≤ 2 * mu A * xi S * entrySupNorm E.1 := by
          have hh := mul_le_mul_of_nonneg_left (support_spectral_le E.2) (show 0 ≤ 2 * xi S by positivity)
          nlinarith
    apply Subtype.ext
    apply (entry_eq_zero_iff E.1).mp
    nlinarith [entry_nonneg E.1]
  let rhs : supportSpace A := ⟨γ • entrySign A - projOmega A (signMatrix S),
    (supportSpace A).sub_mem (omega_smul (sign_omega A) γ) (omega_mem _ _)⟩
  obtain ⟨E, hE⟩ := (LinearMap.injective_iff_surjective.mp hL) rhs
  have heq : E.1 - projOmega A (tangentProjection S E.1) =
      γ • entrySign A - projOmega A (signMatrix S) := congrArg Subtype.val hE
  let F := signMatrix S - tangentProjection S E.1
  have hF : InT S F := by
    rw [inT_iff_tangent_eq]
    dsimp [F]
    rw [tangent_sub, (inT_iff_tangent_eq S _).mp (sign_inT S), tangent_idem]
  have hoeq : projOmega A (E.1 + F) = γ • entrySign A := by
    rw [omega_add, omega_eq_self E.2]
    dsimp [F]
    rw [omega_sub_map]
    apply sub_eq_zero.mp
    have hh := congrArg (fun X : RealMatrix n n => X + projOmega A (signMatrix S)) heq
    simp only [sub_add_cancel] at hh
    calc
      _ = (E.1 - projOmega A (tangentProjection S E.1) + projOmega A (signMatrix S)) -
          γ • entrySign A := by abel
      _ = 0 := by rw [hh, sub_self]
  have hteq : tangentProjection S (E.1 + F) = signMatrix S := by
    rw [tangent_add, (inT_iff_tangent_eq S F).mp hF]
    dsimp [F]
    abel
  have he : entrySupNorm E.1 ≤ γ + xi S * spectralNorm F := by
    have he' : E.1 = γ • entrySign A - projOmega A F := by
      have hh := congrArg (fun X : RealMatrix n n => X + projOmega A (signMatrix S)) heq
      simp only [sub_add_cancel] at hh
      dsimp [F]
      rw [omega_sub_map]
      calc
        _ = (E.1 - projOmega A (tangentProjection S E.1) + projOmega A (signMatrix S)) -
            (projOmega A (signMatrix S) - projOmega A (tangentProjection S E.1)) := by abel
        _ = _ := by rw [hh]
    calc
      _ = entrySupNorm (γ • entrySign A + -(projOmega A F)) := by rw [← sub_eq_add_neg, ← he']
      _ ≤ entrySupNorm (γ • entrySign A) + entrySupNorm (-(projOmega A F)) := entry_add_le _ _
      _ ≤ γ + xi S * spectralNorm F := by
        rw [entry_smul, abs_of_pos hg, entry_neg]
        have hm := omega_entry_le A F
        have ht := tangent_entry_le hF
        have hs := mul_le_mul_of_nonneg_left (sign_entry_le A) hg.le
        nlinarith
  have hf : spectralNorm F ≤ 1 + 2 * mu A * entrySupNorm E.1 := by
    have hneg : spectralNorm (-tangentProjection S E.1) = spectralNorm (tangentProjection S E.1) := by
      have hh := spectral_smul (-1) (tangentProjection S E.1)
      simpa using hh
    change spectralNorm (signMatrix S - tangentProjection S E.1) ≤ _
    rw [sub_eq_add_neg]
    have hsum := spectral_add_le (signMatrix S) (-tangentProjection S E.1)
    rw [hneg] at hsum
    have hp := tangent_spectral_le S E.1
    have hs := support_spectral_le E.2
    nlinarith [sign_spectral_le S]
  have he_bound : (1 - 2 * mu A * xi S) * entrySupNorm E.1 ≤ γ + xi S := by
    have hh := mul_le_mul_of_nonneg_left hf hb
    nlinarith
  have hf_bound : (1 - 2 * mu A * xi S) * spectralNorm F ≤ 1 + 2 * γ * mu A := by
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * mu A by positivity)
    nlinarith
  have hea : mu A * entrySupNorm E.1 < 1 := by
    have hh := mul_le_mul_of_nonneg_left he_bound ha
    nlinarith
  have hfb : xi S * spectralNorm F < γ := by
    have hh := mul_le_mul_of_nonneg_left hf_bound hb
    nlinarith
  refine ⟨E.1 + F, hoeq, hteq, ?_, ?_⟩
  · have hn : normalProjection S (E.1 + F) = normalProjection S E.1 := by
      rw [normal_add, (normal_eq_zero_iff_inT S F).mpr hF, add_zero]
    rw [hn]
    exact (normal_spectral_le S E.1).trans_lt ((support_spectral_le E.2).trans_lt hea)
  · have hc : projOmegaC A (E.1 + F) = projOmegaC A F := by
      change E.1 + F - projOmega A (E.1 + F) = F - projOmega A F
      rw [omega_add, omega_eq_self E.2]
      abel
    rw [hc]
    exact (omegaC_entry_le A F).trans_lt ((tangent_entry_le hF).trans_lt hfb)

end RankSparsityProof

namespace RankSparsityProof

theorem parameter_interval {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a * b < 1 / 6) :
    b / (1 - 4 * a * b) < Real.sqrt (3 * b / (2 * a)) ∧
      Real.sqrt (3 * b / (2 * a)) < (1 - 3 * a * b) / a := by
  have hd : 0 < 1 - 4 * a * b := by nlinarith
  have hden : 0 < 2 * a := by positivity
  have hr : 0 < 3 * b / (2 * a) := by positivity
  have hs := Real.sq_sqrt hr.le
  have hsn := Real.sqrt_nonneg (3 * b / (2 * a))
  have h1 : b / (1 - 4 * a * b) < 3 * b := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos hb (show 0 < 1 - 6 * a * b by nlinarith)]
  have h2 : 3 * b < Real.sqrt (3 * b / (2 * a)) := by
    have hsq : (3 * b) ^ 2 < 3 * b / (2 * a) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith [mul_pos hb (show 0 < 1 - 6 * a * b by nlinarith)]
    nlinarith
  have h3 : Real.sqrt (3 * b / (2 * a)) < 1 / (2 * a) := by
    have hinv : 0 < 1 / (2 * a) := by positivity
    have he : (1 / (2 * a)) * (2 * a) = 1 := div_mul_cancel₀ _ (ne_of_gt hden)
    have hdv : (3 * b / (2 * a)) * (2 * a) = 3 * b :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hsq : 3 * b / (2 * a) < (1 / (2 * a)) ^ 2 := by
      apply (mul_lt_mul_iff_left₀ hden).mp
      nlinarith [mul_pos hinv (show 0 < 1 - 6 * a * b by nlinarith)]
    nlinarith
  have h4 : 1 / (2 * a) < (1 - 3 * a * b) / a := by
    apply (div_lt_div_iff₀ hden ha).mpr
    nlinarith [mul_pos ha (show 0 < 1 - 6 * a * b by nlinarith)]
  exact ⟨h1.trans h2, h3.trans h4⟩

end RankSparsityProof

open MatrixCompletion RankSparsity.Recovery
open scoped BigOperators Classical

namespace RankSparsityProof

lemma strict_recovery {n r : ℕ} (A : RealMatrix n n) {B : RealMatrix n n} (S : SVD B r)
    (γ : ℝ) (hγ : 0 < γ)
    (htrans : ∀ H, InOmega A H → InT S H → H = 0)
    (Q : RealMatrix n n) (hΩ : projOmega A Q = γ • entrySign A)
    (hT : tangentProjection S Q = signMatrix S)
    (hN : spectralNorm (normalProjection S Q) < 1)
    (hC : entrySupNorm (projOmegaC A Q) < γ) :
    IsUniqueOptimum γ (A+B) A B := by
  refine ⟨rfl, ?_⟩
  intro A' B' hsum hne
  let H := B'-B
  have hB : B' = B+H := by dsimp [H]; abel
  have hA : A' = A-H := by
    rw [hB] at hsum
    ext i j
    have he := congrFun (congrFun hsum i) j
    simp only [Matrix.add_apply] at he
    change A' i j = A i j - H i j
    linarith
  have hH : H ≠ 0 := by
    intro hz
    apply hne
    rw [hA, hB, hz, sub_zero, add_zero]
  have hlin : matrixInner (signMatrix S) H - γ*matrixInner (entrySign A) H =
      matrixInner (projOmegaC A Q) H - matrixInner (normalProjection S Q) H := by
    change _ = matrixInner (Q-projOmega A Q) H -
      matrixInner (Q-tangentProjection S Q) H
    rw [inner_sub_left, inner_sub_left, hΩ, hT,
      inner_smul_left]
    ring
  have hcidem : projOmegaC A (projOmegaC A Q) = projOmegaC A Q := by
    ext i j
    simp only [omegaC_apply]
    split_ifs <;> rfl
  have hci : matrixInner (projOmegaC A Q) H =
      matrixInner (projOmegaC A Q) (projOmegaC A H) := by
    rw [← omegaC_inner, hcidem]
  have hni : matrixInner (normalProjection S Q) H =
      matrixInner (normalProjection S Q) (normalProjection S H) := by
    rw [← normal_inner, normal_idem]
  have hcBound := entry_inner_bound (projOmegaC A Q) (projOmegaC A H)
  have hnBound := inner_le_spectral_mul_nuclear (normalProjection S Q) (normalProjection S H)
  rw [← hci] at hcBound
  rw [← hni] at hnBound
  have hl := l1_support_gap A H
  have hng := nuclear_normal_gap S H
  have hgl := mul_le_mul_of_nonneg_left hl (le_of_lt hγ)
  have hl0 := l1_nonneg (projOmegaC A H)
  have hn0 := nuclear_nonneg (normalProjection S H)
  have hpos : 0 < (γ-entrySupNorm (projOmegaC A Q))*l1Norm (projOmegaC A H) +
      (1-spectralNorm (normalProjection S Q))*nuclearNorm (normalProjection S H) := by
    have ha : 0 < γ-entrySupNorm (projOmegaC A Q) := sub_pos.mpr hC
    have hb : 0 < 1-spectralNorm (normalProjection S Q) := sub_pos.mpr hN
    by_cases hz : projOmegaC A H = 0
    · have hnz : normalProjection S H ≠ 0 := by
        intro hnz
        exact hH (htrans H ((omegaC_eq_zero_iff A H).mp hz)
          ((normal_eq_zero_iff_inT S H).mp hnz))
      have hnpos : 0 < nuclearNorm (normalProjection S H) :=
        lt_of_le_of_ne hn0 (Ne.symm (mt (nuclear_eq_zero_iff _).mp hnz))
      exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt ha) hl0) (mul_pos hb hnpos)
    · have hlpos : 0 < l1Norm (projOmegaC A H) :=
        lt_of_le_of_ne hl0 (Ne.symm (mt (l1_eq_zero_iff _).mp hz))
      exact add_pos_of_pos_of_nonneg (mul_pos ha hlpos) (mul_nonneg (le_of_lt hb) hn0)
  rw [hA, hB]
  unfold objective
  have hcneg := neg_le_abs (matrixInner (projOmegaC A Q) H)
  have hnle := le_abs_self (matrixInner (normalProjection S Q) H)
  nlinarith

end RankSparsityProof

open MatrixCompletion

namespace RankSparsity.Recovery

/-- Theorem 2 (p. 10): if `μ(A⋆) ξ(B⋆) < 1/6`, then for every
`γ ∈ (ξ(B⋆)/(1 - 4μ(A⋆)ξ(B⋆)), (1 - 3μ(A⋆)ξ(B⋆))/μ(A⋆))` the unique optimum of (1.3)
with `C = A⋆ + B⋆` is `(A⋆, B⋆)`; and (for `A⋆, B⋆ ≠ 0`) `γ = √(3ξ(B⋆)/(2μ(A⋆)))` lies in
that range. The upper end is written multiplied out, `γ μ(A⋆) < 1 - 3μ(A⋆)ξ(B⋆)`. -/
theorem theorem_2 {n r : ℕ} (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1 / 6) :
    (∀ γ : ℝ, xi S / (1 - 4 * mu Astar * xi S) < γ →
        γ * mu Astar < 1 - 3 * mu Astar * xi S →
        IsUniqueOptimum γ (Astar + Bstar) Astar Bstar) ∧
    (Astar ≠ 0 → Bstar ≠ 0 →
        xi S / (1 - 4 * mu Astar * xi S) < Real.sqrt (3 * xi S / (2 * mu Astar)) ∧
        Real.sqrt (3 * xi S / (2 * mu Astar)) < (1 - 3 * mu Astar * xi S) / mu Astar) := by
  constructor
  · intro γ hl hu
    obtain ⟨Q, hΩ, hT, hN, hC⟩ := RankSparsityProof.certificate Astar S h γ hl hu
    apply RankSparsityProof.strict_recovery Astar S γ
      (RankSparsityProof.parameter_pos Astar S h hl)
      (RankSparsityProof.support_tangent_zero Astar S (by linarith)) Q hΩ hT hN hC
  · intro hA hB
    exact RankSparsityProof.parameter_interval (RankSparsityProof.mu_pos hA)
      (RankSparsityProof.xi_pos S hB) h

end RankSparsity.Recovery

open RankSparsity.Recovery

theorem solution {n r : ℕ} (Astar Bstar : RealMatrix n n) (S : SVD Bstar r)
    (h : mu Astar * xi S < 1 / 6) :
    (∀ γ : ℝ, xi S / (1 - 4 * mu Astar * xi S) < γ →
        γ * mu Astar < 1 - 3 * mu Astar * xi S →
        IsUniqueOptimum γ (Astar + Bstar) Astar Bstar) ∧
    (Astar ≠ 0 → Bstar ≠ 0 →
        xi S / (1 - 4 * mu Astar * xi S) < Real.sqrt (3 * xi S / (2 * mu Astar)) ∧
        Real.sqrt (3 * xi S / (2 * mu Astar)) < (1 - 3 * mu Astar * xi S) / mu Astar) := by
  exact RankSparsity.Recovery.theorem_2 Astar Bstar S h
