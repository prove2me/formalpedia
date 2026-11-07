-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_interior_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:28.467201+00:00
-- url     : https://prove2.me/submissions/ee9aaa49-fece-4265-bfe1-58c0e6b2a139

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_ofComplex_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  have he : (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledInteriorChart N hN x).symm w))=
      lpsOriginalJInvariant∘UpperHalfPlane.ofComplex := by
    funext w
    rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledJ_projection]
    rfl
  rw [he]
  exact lpsOriginalJInvariant_ofComplex_analytic
    ⟨z,lpsOriginalFilledInteriorChart_target_pos N hN x z hz⟩
end QEC.Coding.TannerLiftedProduct
