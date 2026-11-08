-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedQuotient_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:05:04.57144+00:00
-- url     : https://prove2.me/submissions/bb65e568-2c1a-4deb-ab28-8517d51ee0d3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalJDilatedQuotient N hN ⟦τ⟧=lpsOriginalJDilated N hN τ := rfl
end QEC.Coding.TannerLiftedProduct
