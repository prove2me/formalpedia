-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_disk_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:19:17.80312+00:00
-- url     : https://prove2.me/submissions/0cd0e5d9-2c0c-4dc9-94d0-5ae22ed774da

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_pullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) {q : ℂ} (hq : ‖q‖<1) (hq0 : q≠0) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P q=0 := by
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
  have hqτ : Function.Periodic.qParam 1 (τ:ℂ)=q :=
    Function.Periodic.qParam_right_inv (by norm_num) hq0
  rw [←hqτ,lpsOriginalClearedCusp_pullback N hN P τ,hroot,mul_zero]
end QEC.Coding.TannerLiftedProduct
