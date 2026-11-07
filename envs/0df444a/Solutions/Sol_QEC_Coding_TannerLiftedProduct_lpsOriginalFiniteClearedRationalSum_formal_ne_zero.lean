-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_formal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:38:49.61023+00:00
-- url     : https://prove2.me/submissions/f4c8efb0-b54e-4575-be27-c840ea2494d6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroGerm_of_puncturedDisk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B)
    (hs : (∑ i, PowerSeries.C (a i) *
      lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) ≠ 0) :
    lpsOriginalRationalMonomialHolomorphicSum M hM u v a ≠ 0 := by
  intro hz
  have hg : lpsOriginalFiniteClearedRationalSum M B u v a =ᶠ[𝓝 0] 0 := by
    apply lpsOriginalZeroGerm_of_puncturedDisk
      (lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v a)
    intro q hq hq0
    let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqτ : Function.Periodic.qParam 1 (τ : ℂ) = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    rw [← hqτ, lpsOriginalFiniteClearedRationalSum_pullback M hM B u v a hB τ, hz]
    exact mul_zero _
  have ht := (lpsOriginalTaylorSeries_zero_iff_germ
    (lpsOriginalFiniteClearedRationalSum_analytic M (Nat.ne_of_gt hM) B u v a)).mpr hg
  rw [lpsOriginalFiniteClearedRationalSum_taylor M (Nat.ne_of_gt hM)] at ht
  apply hs
  exact PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    (ht.trans (map_zero _).symm)
end QEC.Coding.TannerLiftedProduct
