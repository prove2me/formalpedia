-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAffinePhaseEquality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:33:56.348265+00:00
-- url     : https://prove2.me/submissions/6f43c053-928c-42d9-8ab4-6459abd273de

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineNome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_qParam_pullback


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0 < m)
    (r s : ℝ)
    (he : Function.Periodic.qParam 1 (r : ℂ) = Function.Periodic.qParam 1 (s : ℂ))
    (τ : ℍ) :
    lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ) =
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm s • τ) := by
  have hq : Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm s • τ : ℍ) : ℂ) := by
    rw [lpsOriginalAffineNome, lpsOriginalAffineNome, he]
  apply mul_left_cancel₀ (Function.Periodic.qParam_ne_zero
    (h := 1) ((lpsE2AffineMatrix m hm r • τ : ℍ) : ℂ))
  rw [lpsOriginalJInvariant_qParam_pullback, hq, lpsOriginalJInvariant_qParam_pullback]
end QEC.Coding.TannerLiftedProduct
