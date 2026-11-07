-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForgetLevel_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:28:11.436203+00:00
-- url     : https://prove2.me/submissions/af4af8c7-881d-47b6-ba72-5880173cf590

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspForgetLevel_projection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) : Function.Surjective (lpsOriginalCuspForgetLevel N M hNM) := by
  intro c
  obtain ⟨ρ, rfl⟩ := lpsOriginalCuspOrbit_surjective N c
  exact ⟨lpsOriginalCuspOrbit M ρ, lpsOriginalCuspForgetLevel_projection N M hNM ρ⟩
end QEC.Coding.TannerLiftedProduct
