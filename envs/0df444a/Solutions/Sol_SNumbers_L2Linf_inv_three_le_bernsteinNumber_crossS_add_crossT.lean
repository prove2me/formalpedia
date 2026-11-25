-- Prove2me | solution 1 for SNumbers.L2Linf.inv_three_le_bernsteinNumber_crossS_add_crossT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:46:43.123374+00:00
-- url     : https://prove2.me/submissions/51d4fa88-8e55-4617-8a6b-68adf925c5d3

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_crossS_add_crossT_graphThree
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bddAbove_bernsteinSet
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_finrank_piLp
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_le_gainOnSubspace
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution :
    (3 : ℝ)⁻¹ ≤ bernsteinNumber (crossS (𝕜 := 𝕜) + crossT) (35 + 35) := by
  set E : Submodule 𝕜 (L2LinfProd 𝕜) :=
    LinearMap.range (graphThree (𝕜 := 𝕜) : PiLp 2 (fun _ : Fin 71 => 𝕜) →ₗ[𝕜] L2LinfProd 𝕜)
    with hE
  have hinj : Function.Injective
      (graphThree (𝕜 := 𝕜) : PiLp 2 (fun _ : Fin 71 => 𝕜) →ₗ[𝕜] L2LinfProd 𝕜) :=
    fun x y h => congrArg Prod.fst h
  have hE_rank : Module.rank 𝕜 E = ((35 + 35 + 1 : ℕ) : Cardinal) := by
    rw [hE, rank_range_of_injective _ hinj, ← Module.finrank_eq_rank, finrank_piLp]
  have hE_ne : E ≠ ⊥ := fun h => by
    rw [h, rank_bot] at hE_rank
    exact Nat.succ_ne_zero (35 + 35) (by exact_mod_cast hE_rank.symm)
  refine le_trans ?_ (le_csSup (bddAbove_bernsteinSet _ _) ⟨E, hE_rank, rfl⟩)
  refine le_gainOnSubspace hE_ne fun z hz hz0 => ?_
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
  simp only [ContinuousLinearMap.coe_coe] at hz0 ⊢
  rw [crossS_add_crossT_graphThree, norm_smul, mul_div_assoc,
    div_self (norm_ne_zero_iff.mpr hz0), mul_one, norm_inv, RCLike.norm_ofNat]
end SNumbers.L2Linf
