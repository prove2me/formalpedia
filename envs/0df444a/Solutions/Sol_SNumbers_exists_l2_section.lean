-- Prove2me | solution 1 for SNumbers.exists_l2_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:43:11.173252+00:00
-- url     : https://prove2.me/submissions/61fbc84f-6d1c-48c4-b16e-1bd28fbc2387

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (n : ℕ) :
    ∃ (B : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L2 𝕜)
      (A : L2 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))),
      A.comp B = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ∧
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 := by
  classical
  -- The first `n+1` standard basis vectors of `ℓ₂`, an orthonormal family.
  set s : Fin (n + 1) → L2 𝕜 := fun k => lp.single 2 (k : ℕ) (1 : 𝕜) with hsdef
  have hs : Orthonormal 𝕜 s := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [hsdef, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    by_cases h : i = j
    · rw [if_pos h, h, lp.single_apply_self]
    · rw [if_neg h]
      exact lp.single_apply_ne _ _ _ (fun he => h (Fin.ext he))
  -- The embedding `f v = Σ vₖ · eₖ`, as an inner-preserving linear map.
  set f : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] L2 𝕜 :=
    ∑ k : Fin (n + 1),
      (innerSL 𝕜 (EuclideanSpace.single k (1 : 𝕜))).toLinearMap.smulRight (s k) with hfdef
  have hf_apply : ∀ v, f v = ∑ k : Fin (n + 1), v k • s k := by
    intro v
    rw [hfdef]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul]
  have hf : ∀ x y, (inner 𝕜 (f x) (f y) : 𝕜) = inner 𝕜 x y := by
    intro x y
    rw [hf_apply x, hf_apply y, sum_inner]
    simp_rw [inner_smul_left, hs.inner_right_sum y (Finset.mem_univ _)]
    rw [PiLp.inner_apply]
    simp_rw [RCLike.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- Package as a linear isometry; its adjoint is the contraction `A`.
  set Bᵢ : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗᵢ[𝕜] L2 𝕜 := LinearMap.isometryOfInner f hf with hBᵢ
  refine ⟨Bᵢ.toContinuousLinearMap, (Bᵢ.toContinuousLinearMap).adjoint, ?_, ?_, ?_⟩
  · exact LinearIsometry.adjoint_comp_self Bᵢ
  · rw [LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [LinearIsometry.coe_toContinuousLinearMap, Bᵢ.norm_map, one_mul]
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [LinearIsometry.coe_toContinuousLinearMap, Bᵢ.norm_map, one_mul]
end SNumbers
