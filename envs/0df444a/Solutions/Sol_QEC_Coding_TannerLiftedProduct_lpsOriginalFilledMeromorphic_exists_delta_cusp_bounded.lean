-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:40:23.376902+00:00
-- url     : https://prove2.me/submissions/b0a71ecd-f9af-45ad-8ab8-44fbdf807d8d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_delta_cusp_bounded
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ k : ℕ, ∀ ρ : SL(2,ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  obtain ⟨k,hk⟩ := lpsOriginalFilledMeromorphic_uniform_cusp_pole_clearing N hN F hF
  exact ⟨k,fun ρ => lpsOriginalFilledMeromorphic_delta_cusp_bounded N ρ F k
    (hk (lpsOriginalCuspOrbit N ρ))⟩
end QEC.Coding.TannerLiftedProduct
