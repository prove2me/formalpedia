-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nucNorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T03:32:19.726313+00:00
-- url     : https://prove2.me/submissions/3790bf37-7ed2-40c7-9868-6576e5e85058

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

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

noncomputable def makeU {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) : E₂ →ₗ[ℝ] E₁ :=
  ∑ j : ι, LinearMap.smulRight (innerSL ℝ (b j)).toLinearMap (u j)

theorem makeU_apply {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) (x : E₂) :
    makeU b u x = ∑ j : ι, @inner ℝ E₂ _ (b j) x • u j := by
  simp [makeU]

theorem makeU_basis {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁) (i : ι) :
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

theorem norm_makeU_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E₂) (u : ι → E₁)
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

theorem nucNorm_add_le {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    nucNorm (A + B) ≤ nucNorm A + nucNorm B := by
  set C := A + B
  set TC := Matrix.toEuclideanLin C
  set hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) = d₂ := by simp [finrank_euclideanSpace]
  set b := (TC.isSymmetric_adjoint_comp_self).eigenvectorBasis hn
  set u : Fin d₂ → EuclideanSpace ℝ (Fin d₁) := fun i => ‖TC (b i)‖⁻¹ • TC (b i)
  have h_ortho : ∀ i j : Fin d₂, i ≠ j → @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (u i) (u j) = 0 := by
    intro i j hij
    dsimp [u]
    rw [inner_smul_left, inner_smul_right, conj_trivial]
    have h_adj : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TC (b i)) (TC (b j)) =
        @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ (b i) ((TC.adjoint ∘ₗ TC) (b j)) := by
      exact (LinearMap.adjoint_inner_right TC (b i) (TC (b j))).symm
    have h_eig : (TC.adjoint ∘ₗ TC) (b j) = (TC.isSymmetric_adjoint_comp_self.eigenvalues hn j) • b j :=
      TC.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn j
    rw [h_adj, h_eig, inner_smul_right]
    have h_b_ortho : @inner ℝ (EuclideanSpace ℝ (Fin d₂)) _ (b i) (b j) = 0 :=
      b.orthonormal.2 hij
    rw [h_b_ortho]
    ring
  have h_norm : ∀ i : Fin d₂, ‖u i‖ ≤ 1 := by
    intro i
    dsimp [u]
    rw [norm_smul]
    by_cases h0 : ‖TC (b i)‖ = 0
    · rw [h0, inv_zero, norm_zero, mul_zero]
      exact zero_le_one
    · have hpos : 0 < ‖TC (b i)‖ := (norm_nonneg _).lt_of_ne' h0
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ h0]
  have h_inner_self : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TC (b i)) (u i) = ‖TC (b i)‖ := by
    intro i
    dsimp [u]
    rw [inner_smul_right]
    have h_sq : @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TC (b i)) (TC (b i)) = ‖TC (b i)‖ ^ 2 := by
      rw [real_inner_self_eq_norm_mul_norm, ← sq]
    rw [h_sq]
    by_cases h0 : ‖TC (b i)‖ = 0
    · rw [h0, inv_zero]
      ring
    · rw [sq, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  set U := makeU b u
  have hU_contract : ∀ x, ‖U x‖ ≤ ‖x‖ := norm_makeU_le b u h_ortho h_norm
  have h_trace_C : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) (TC.adjoint.comp U) = nucNorm C := by
    rw [← sum_inner_eq_trace TC U b]
    have h_eval : ∀ i : Fin d₂, @inner ℝ (EuclideanSpace ℝ (Fin d₁)) _ (TC (b i)) (U (b i)) =
        TC.singularValues i := by
      intro i
      rw [makeU_basis b u i, h_inner_self i]
      exact norm_toEuclideanLin_apply_eigenvectorBasis C i
    simp_rw [h_eval]
    exact sum_singularValues_eq_nucNorm C
  have h_lin_add : (Matrix.toEuclideanLin C).adjoint.comp U =
      (Matrix.toEuclideanLin A).adjoint.comp U + (Matrix.toEuclideanLin B).adjoint.comp U := by
    dsimp [C]
    rw [map_add, map_add LinearMap.adjoint, LinearMap.add_comp]
  have h_trace_add : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) (TC.adjoint.comp U) =
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin A).adjoint.comp U) +
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin B).adjoint.comp U) := by
    change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d₂)) ((Matrix.toEuclideanLin C).adjoint.comp U) = _
    rw [h_lin_add, map_add]
  have h_le_A := trace_adjoint_comp_le_nucNorm A U hU_contract
  have h_le_B := trace_adjoint_comp_le_nucNorm B U hU_contract
  dsimp [C] at h_trace_C
  rw [← h_trace_C, h_trace_add]
  exact add_le_add h_le_A h_le_B

abbrev solution := @nucNorm_add_le

end WainwrightHDS.NucNorm

abbrev solution := @WainwrightHDS.NucNorm.nucNorm_add_le
