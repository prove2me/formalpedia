-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_interior_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:14:25.335402+00:00
-- url     : https://prove2.me/submissions/865903fa-b351-46d5-be56-56bc33b5f064

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_ofComplex_analytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 4∣N) (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  have he : (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledInteriorChart N hN x).symm w))=
      (fun w => (lpsOriginalJInvariant (UpperHalfPlane.ofComplex w)-a)⁻¹) := by
    funext w
    rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledJReciprocal_projection]
  rw [he]
  have hj := lpsOriginalJInvariant_ofComplex_analytic
    ⟨z,lpsOriginalFilledInteriorChart_target_pos N hN x z hz⟩
  exact (hj.sub analyticAt_const).inv (sub_ne_zero.mpr (ho (UpperHalfPlane.ofComplex z)))
end QEC.Coding.TannerLiftedProduct
