-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphic_delta_j_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:33:58.93448+00:00
-- url     : https://prove2.me/submissions/6811dee8-b2ee-40ab-8ad9-d6674dd66642

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDelta_j_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4PowerHolomorphic_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (k : ℕ) :
    lpsOriginalDeltaHolomorphic^k * lpsOriginalJHolomorphic^k =
      lpsOriginalE4PowerHolomorphic k := by
  apply Subtype.ext
  funext τ
  change ModularForm.discriminant τ^k * lpsOriginalJInvariant τ^k = _
  rw [lpsOriginalE4PowerHolomorphic_apply]
  exact lpsOriginalDelta_j_power k τ
end QEC.Coding.TannerLiftedProduct
