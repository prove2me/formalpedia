-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranch_infty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:25:52.436852+00:00
-- url     : https://prove2.me/submissions/8eedf1af-bd4b-487f-ac7e-aa5c5a8833a1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    lpsOriginalPrimeBranch p none τ=lpsOriginalJDilated p (Fact.out : p.Prime).pos τ := by
  rw [lpsOriginalPrimeBranch,lpsHeckeUpperGL_infty]
  rfl
end QEC.Coding.TannerLiftedProduct
