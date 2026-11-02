-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P02.compact_modulus_spectral_expansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:01.405175+00:00
-- url     : https://prove2.me/submissions/2e77301f-7349-456d-b5d5-4a398cd62423

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section
open Set Metric Module.End
open scoped InnerProductSpace Topology
universe u v w

namespace Helpers
variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

noncomputable def get_basis (T : E →L[𝕜] E) (μ : 𝕜) :
    Σ (w : Set (Module.End.eigenspace (T : Module.End 𝕜 E) μ)),
      HilbertBasis w 𝕜 (Module.End.eigenspace (T : Module.End 𝕜 E) μ) := by
  haveI : CompleteSpace (Module.End.eigenspace (T : Module.End 𝕜 E) μ) :=
    IsClosed.completeSpace_coe (hs := ContinuousLinearMap.isClosed_eigenspace T μ)
  have h := exists_hilbertBasis 𝕜 (Module.End.eigenspace (T : Module.End 𝕜 E) μ)
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

noncomputable def v' (T : E →L[𝕜] E) (p : Σ (μ : 𝕜), (get_basis T μ).1) : E :=
  ((get_basis T p.1).2 p.2 : E)

lemma v'_orthonormal (T : E →L[𝕜] E) (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    Orthonormal 𝕜 (v' T) :=
  OrthogonalFamily.orthonormal_sigma_orthonormal
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces hsym)
    (fun μ => (get_basis T μ).2.orthonormal)

lemma v'_eigenvector (T : E →L[𝕜] E) (p : Σ (μ : 𝕜), (get_basis T μ).1) :
    T (v' T p) = p.1 • v' T p :=
  Module.End.mem_eigenspace_iff.mp ((get_basis T p.1).2 p.2).2

lemma orthogonal_eigenspace (T : E →L[𝕜] E) (x : E)
    (hx : x ∈ (Submodule.span 𝕜 (Set.range (v' T)))ᗮ) (μ : 𝕜) :
    x ∈ (Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
  let W := Module.End.eigenspace (T : Module.End 𝕜 E) μ
  rw [Submodule.mem_orthogonal']
  intro y hy
  let y_W : W := ⟨y, hy⟩
  let b := (get_basis T μ).2
  have hsum := ((b.hasSum_repr y_W).mapL W.subtypeL).mapL (innerSL 𝕜 x)
  have hzero (i : (get_basis T μ).1) : ⟪x, W.subtype (b i)⟫_𝕜 = 0 := by
    have h_mem : W.subtype (b i) ∈ Submodule.span 𝕜 (Set.range (v' T)) :=
      Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal h_mem hx
  have hzero' (i : (get_basis T μ).1) :
      (innerSL 𝕜 x) (W.subtypeL (b.repr y_W i • b i)) = 0 := by
    rw [map_smul, Submodule.coe_subtypeL, innerSL_apply_apply, inner_smul_right, hzero, mul_zero]
  simp only [hzero'] at hsum
  have h_inner : ⟪x, y⟫_𝕜 = 0 := hsum.unique hasSum_zero
  exact h_inner

lemma orthogonalComplement_span_range_v'_eq_bot (T : E →L[𝕜] E)
    (hT : IsCompactOperator T) (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (Submodule.span 𝕜 (Set.range (v' T)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h_orth (μ : 𝕜) : x ∈ (Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ :=
    orthogonal_eigenspace T x hx μ
  have h_iInf : x ∈ ⨅ μ, (Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ := by
    rw [Submodule.mem_iInf]
    exact h_orth
  rw [Submodule.iInf_orthogonal] at h_iInf
  have h_bot : (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym
  rw [h_bot, Submodule.mem_bot] at h_iInf
  exact h_iInf

theorem eigenbasis_set_real (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (μ : s → ℝ),
      ∀ j, T (b j) = (μ j : 𝕜) • b j := by
  let s := Set.range (v' T)
  have hv' : Orthonormal 𝕜 (v' T) := v'_orthonormal T hsym
  let e : s ≃ (Σ (μ : 𝕜), (get_basis T μ).1) :=
    (Equiv.ofInjective (v' T) hv'.linearIndependent.injective).symm
  let v : s → E := v' T ∘ e
  have hv : Orthonormal 𝕜 v := hv'.comp e e.injective
  have h_range : Set.range v = Set.range (v' T) := e.surjective.range_comp (v' T)
  have hbot : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    rw [h_range]
    exact orthogonalComplement_span_range_v'_eq_bot T hT hsym
  let b : HilbertBasis s 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hv hbot
  have hb : (b : s → E) = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv hbot
  have heig (j : s) : T (b j) = (e j).1 • b j := by
    rw [congr_fun hb j]
    exact v'_eigenvector T (e j)
  refine ⟨s, b, fun j ↦ RCLike.re (e j).1, fun j ↦ ?_⟩
  have he : HasEigenvalue (T : Module.End 𝕜 E) (e j).1 :=
    hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (heig j), b.orthonormal.ne_zero j⟩
  have hr : ((RCLike.re (e j).1 : ℝ) : 𝕜) = (e j).1 :=
    RCLike.conj_eq_iff_re.mp (hsym.conj_eigenvalue_eq_self he)
  rw [hr]
  exact heig j

variable {G : Type w} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

theorem compact_of_adjoint_comp (T : E →L[𝕜] G) (hT : IsCompactOperator (T.adjoint ∘L T)) :
    IsCompactOperator T := by
  classical
  let A := T.adjoint ∘L T
  let S : Set E := closedBall 0 1
  have hA : TotallyBounded (A '' S) := by
    apply (hT.isCompact_closure_image_closedBall 1).totallyBounded.subset
    exact subset_closure
  have hineq : ∀ x ∈ S, ∀ y ∈ S, ‖T x - T y‖ ^ 2 ≤ 2 * ‖A x - A y‖ := by
    intro x hx y hy
    have hx' : ‖x‖ ≤ 1 := by simpa [S, mem_closedBall, dist_zero_right] using hx
    have hy' : ‖y‖ ≤ 1 := by simpa [S, mem_closedBall, dist_zero_right] using hy
    have hxy : ‖x - y‖ ≤ 2 := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    calc
      ‖T x - T y‖ ^ 2 = RCLike.re ⟪A (x - y), x - y⟫_𝕜 := by
        simpa [A, map_sub] using T.apply_norm_sq_eq_inner_adjoint_left (x - y)
      _ ≤ ‖A (x - y)‖ * ‖x - y‖ := re_inner_le_norm _ _
      _ ≤ 2 * ‖A x - A y‖ := by
        rw [map_sub]
        nlinarith [norm_nonneg (A x - A y)]
  have hcompact : TotallyBounded (T '' S) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨s, hsS, hsfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hA (ε^2 / 4) (by positivity)
    choose f hf using fun z : s => hsS z.property
    have : Finite s := hsfin.to_subtype
    refine ⟨(fun z : s => T (f z)) '' univ, Set.finite_univ.image _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxA : A x ∈ A '' S := ⟨x, hx, rfl⟩
    have hxcover := hcover hxA
    simp only [mem_iUnion, mem_ball] at hxcover ⊢
    obtain ⟨z, hz, hdist⟩ := hxcover
    let z' : s := ⟨z, hz⟩
    refine ⟨T (f z'), ⟨z', mem_univ _, rfl⟩, ?_⟩
    have hfz : f z' ∈ S ∧ A (f z') = z := hf z'
    have hi := hineq x hx (f z') hfz.1
    have hd : ‖A x - A (f z')‖ < ε^2 / 4 := by
      simpa [dist_eq_norm, hfz.2] using hdist
    rw [dist_eq_norm]
    nlinarith [sq_nonneg (‖T x - T (f z')‖ - ε)]
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap (by norm_num : (0:ℝ) < 1)).2
  exact (totallyBounded_closure.mpr hcompact).isCompact_of_isClosed isClosed_closure
end Helpers

namespace QAlgorithms.Papers.Independent.Next46.P02
variable {F : Type*} [RCLike F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

theorem _root_.solution (T : H →L[F] H) (hT : IsCompactOperator T) :
    ∃ (s : Set H) (b : HilbertBasis s F H) (mu : s → ℝ),
      (∀ i, 0 ≤ mu i) ∧ ∀ x : H,
        HasSum (fun i => ((mu i : F) * inner F (b i) x) • b i) (hilbertOperatorModulus T x) := by
  classical
  let A := T.adjoint.comp T
  let B := hilbertOperatorModulus T
  have hAc : IsCompactOperator A := by
    exact hT.clm_comp T.adjoint
  have hB : B.IsPositive ∧ IsCompactOperator B := by
    by_cases hz : A = 0
    · have : B = 0 := by
        change hilbertPositiveSqrt A = 0
        simp [hilbertPositiveSqrt, hz]
      rw [this]
      exact ⟨ContinuousLinearMap.isPositive_zero,
        by simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))⟩
    · by_cases he : ∃ C : H →L[F] H, C.IsPositive ∧ C.comp C = A
      · have hb : B = Classical.choose he := by
          change hilbertPositiveSqrt A = Classical.choose he
          simp [hilbertPositiveSqrt, hz, he]
        rw [hb]
        have hp := (Classical.choose_spec he).1
        refine ⟨hp, Helpers.compact_of_adjoint_comp _ ?_⟩
        have hadj : (Classical.choose he).adjoint = Classical.choose he := hp.isSelfAdjoint
        rw [hadj, (Classical.choose_spec he).2]
        exact hAc
      · have : B = 0 := by
          change hilbertPositiveSqrt A = 0
          simp [hilbertPositiveSqrt, hz, he]
        rw [this]
        exact ⟨ContinuousLinearMap.isPositive_zero,
          by simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))⟩
  obtain ⟨s, b, mu, hm⟩ := Helpers.eigenbasis_set_real B hB.2 hB.1.isSymmetric
  refine ⟨s, b, mu, ?_, ?_⟩
  · intro i
    apply eigenvalue_nonneg_of_nonneg (T := (B : H →ₗ[F] H))
    · exact hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hm i), b.orthonormal.ne_zero i⟩
    · exact hB.1.re_inner_nonneg_right
  · intro x
    have hs := (b.hasSum_repr x).mapL B
    convert hs using 1
    ext i
    simp only [Function.comp_apply, map_smul, hm, b.repr_apply_apply, smul_smul]
    rw [mul_comm]
end QAlgorithms.Papers.Independent.Next46.P02
end
