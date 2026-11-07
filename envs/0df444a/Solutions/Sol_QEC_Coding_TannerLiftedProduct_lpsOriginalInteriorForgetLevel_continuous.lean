-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:35.271441+00:00
-- url     : https://prove2.me/submissions/f2e282af-2cab-4a45-8d68-492a3ded6d24

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) (hNM : N ∣ M) :
    Continuous (lpsOriginalInteriorForgetLevel N M hNM) := by
  unfold lpsOriginalInteriorForgetLevel
  exact continuous_id.quotient_map' _
end QEC.Coding.TannerLiftedProduct
