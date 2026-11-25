-- Prove2me | solution 1 for SNumbers.norm_le_hilbertNumber_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:58.502814+00:00
-- url     : https://prove2.me/submissions/02a9f014-f1ea-4574-87c1-e7ae49701106

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_ratio_le_hilbertNumber
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
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
theorem _root_.solution (S : X →L[𝕜] Y) : ‖S‖ ≤ hilbertNumber S 0 := by
  refine S.opNorm_le_bound (hilbertNumber_nonneg S 0) fun x => ?_
  -- Goal: `‖S x‖ ≤ h₀ S * ‖x‖`. Trivial when `S x = 0`.
  by_cases hSx : S x = 0
  · rw [hSx, norm_zero]
    exact mul_nonneg (hilbertNumber_nonneg S 0) (norm_nonneg x)
  have hx : x ≠ 0 := fun h => hSx (by rw [h, map_zero])
  -- First standard basis vector of `ℓ₂`, a unit vector.
  set e₀ : L2 𝕜 := lp.single 2 (0 : ℕ) (1 : 𝕜) with he₀
  have he₀norm : ‖e₀‖ = 1 := by
    rw [he₀, lp.norm_single (show (0 : ENNReal) < 2 by norm_num), norm_one]
  -- Hahn–Banach norming functional for `S x`.
  obtain ⟨φ, hφnorm, hφval⟩ :=
    exists_dual_vector (𝕜 := 𝕜) (S x) (norm_ne_zero_iff.mpr hSx)
  -- The rank-one pair.
  set A : L2 𝕜 →L[𝕜] X := (innerSL 𝕜 e₀).smulRight x with hA
  set B : Y →L[𝕜] L2 𝕜 := φ.smulRight e₀ with hB
  have hAnorm : ‖A‖ = ‖x‖ := by
    rw [hA, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, he₀norm, one_mul]
  have hBnorm : ‖B‖ = 1 := by
    rw [hB, ContinuousLinearMap.norm_smulRight_apply, hφnorm, he₀norm, mul_one]
  have hAne : A ≠ 0 := by rw [← norm_pos_iff, hAnorm]; exact norm_pos_iff.mpr hx
  have hBne : B ≠ 0 := by rw [← norm_pos_iff, hBnorm]; exact one_pos
  -- `A e₀ = x` (since `⟨e₀, e₀⟩ = ‖e₀‖² = 1`).
  have hAe₀ : A e₀ = x := by
    rw [hA, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_self_eq_norm_sq_to_K, he₀norm]
    simp
  -- `(B ∘ S ∘ A) e₀ = ‖S x‖ • e₀`.
  have hBSA_e₀ : (B.comp (S.comp A)) e₀ = (‖S x‖ : 𝕜) • e₀ := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hAe₀, hB, ContinuousLinearMap.smulRight_apply, hφval]
  -- Hence `‖S x‖ ≤ ‖B ∘ S ∘ A‖`.
  have hge : ‖S x‖ ≤ ‖B.comp (S.comp A)‖ := by
    have h := (B.comp (S.comp A)).le_opNorm e₀
    rw [hBSA_e₀, norm_smul, he₀norm, mul_one, mul_one, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)] at h
    exact h
  -- The admissible ratio is `≤ h₀ S`; rearrange.
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hratio := ratio_le_hilbertNumber S 0 hAne hBne
  rw [approximationNumber_zero_eq_norm, hBnorm, hAnorm, one_mul, div_le_iff₀ hxpos] at hratio
  exact le_trans hge hratio
end SNumbers
