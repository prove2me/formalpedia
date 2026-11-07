-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAffineSlopePhaseEquality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:39:05.834201+00:00
-- url     : https://prove2.me/submissions/584a5930-949e-48e3-96bc-2d8266e0b226

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffinePhaseEquality

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hmn : m = n) (r s : ℝ)
    (he : Function.Periodic.qParam 1 (r : ℂ) = Function.Periodic.qParam 1 (s : ℂ))
    (τ : ℍ) :
    lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ) =
      lpsOriginalJInvariant (lpsE2AffineMatrix n hn s • τ) := by
  subst n
  exact lpsOriginalAffinePhaseEquality m hm r s he τ
end QEC.Coding.TannerLiftedProduct
