-- Prove2me | solution 1 for SNumbers.detNumber_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:21:09.362628+00:00
-- url     : https://prove2.me/submissions/9856226f-7626-45ca-80df-9e3350c308c8

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open ContinuousLinearMap
open scoped Pointwise
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
omit [RCLike 𝕜] in
/-- The trivial space `ℓ₂⁰` has only one element. -/
private lemma subsingleton_euclidean_zero :
    Subsingleton (EuclideanSpace 𝕜 (Fin 0)) :=
  ⟨fun _ _ => PiLp.ext fun i => i.elim0⟩
section Border
variable {k : ℕ}
variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)
end Border
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) : detNumber S 0 = 1 := by
  have := subsingleton_euclidean_zero (𝕜 := 𝕜)
  have hset : detSet S 0 = {(1 : ℝ)} := by
    ext r
    constructor
    · rintro ⟨A, B, _, _, rfl⟩
      rw [Set.mem_singleton_iff, LinearMap.det_eq_one_of_subsingleton, norm_one]
    · rintro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨0, 0, by simp, by simp,
        by rw [LinearMap.det_eq_one_of_subsingleton, norm_one]⟩
  rw [detNumber, hset, csSup_singleton]
end SNumbers
