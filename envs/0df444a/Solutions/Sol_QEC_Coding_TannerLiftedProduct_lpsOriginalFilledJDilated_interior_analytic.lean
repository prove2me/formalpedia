-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_interior_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:11.851355+00:00
-- url     : https://prove2.me/submissions/0cc460e5-e288-4f27-be7c-21021b22be2d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_ofComplex_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  have he : (fun w : ℂ => lpsOriginalFilledJDilated N hpos
      ((lpsOriginalFilledInteriorChart N hN x).symm w))=
      (lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex := by
    funext w
    rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledJDilated_projection]
    rfl
  rw [he]
  exact lpsOriginalJDilated_ofComplex_analytic N hpos
    ⟨z,lpsOriginalFilledInteriorChart_target_pos N hN x z hz⟩
end QEC.Coding.TannerLiftedProduct
