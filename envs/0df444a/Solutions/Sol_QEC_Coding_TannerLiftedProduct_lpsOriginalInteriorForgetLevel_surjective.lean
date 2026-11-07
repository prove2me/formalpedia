-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:32.783534+00:00
-- url     : https://prove2.me/submissions/55ef8a65-c149-443c-8f1d-9b9b8db45468

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) (hNM : N ∣ M) :
    Function.Surjective (lpsOriginalInteriorForgetLevel N M hNM) := by
  intro y
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep y
  exact ⟨⟦τ⟧, rfl⟩
end QEC.Coding.TannerLiftedProduct
