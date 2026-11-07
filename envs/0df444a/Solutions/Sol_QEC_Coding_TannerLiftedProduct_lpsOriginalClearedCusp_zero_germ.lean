-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_zero_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:22:47.741787+00:00
-- url     : https://prove2.me/submissions/a149f763-c6b8-4f16-9cb2-899058a74cda

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_disk_zero

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
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P=ᶠ[𝓝 0]0 := by
  let G := lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖<1 := by
    exact (isOpen_lt (continuous_norm : Continuous (fun q : ℂ=>‖q‖)) continuous_const).mem_nhds (by norm_num : ‖(0:ℂ)‖<1)
  have hp : G=ᶠ[𝓝[≠] (0:ℂ)]0 := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
    exact lpsOriginalClearedCusp_disk_zero N hN P hroot hq hq0
  have h0 : G 0=0 := tendsto_nhds_unique_of_eventuallyEq
    ((lpsOriginalClearedCusp_analytic N (Nat.ne_of_gt hN) _ P).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) tendsto_const_nhds hp
  filter_upwards [hsmall] with q hq
  by_cases hq0 : q=0
  · subst q;exact h0
  · exact lpsOriginalClearedCusp_disk_zero N hN P hroot hq hq0
end QEC.Coding.TannerLiftedProduct
