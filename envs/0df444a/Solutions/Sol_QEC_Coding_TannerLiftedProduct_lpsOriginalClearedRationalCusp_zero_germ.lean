-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_zero_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:33:17.168995+00:00
-- url     : https://prove2.me/submissions/3dad5c62-331c-48d9-9451-ba0099f1dcd6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedFormal_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P=ᶠ[𝓝 0]0 := by
  apply (lpsOriginalTaylorSeries_zero_iff_germ
    (lpsOriginalClearedRationalCusp_analytic N (Nat.ne_of_gt hN) _ P)).mp
  rw [lpsOriginalClearedRationalCusp_taylor N (Nat.ne_of_gt hN),lpsOriginalClearedFormal_zero N hN P hroot,
    map_zero]
end QEC.Coding.TannerLiftedProduct
