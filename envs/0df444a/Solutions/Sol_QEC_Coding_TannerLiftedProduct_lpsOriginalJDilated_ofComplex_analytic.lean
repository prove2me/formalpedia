-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_ofComplex_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:10.223974+00:00
-- url     : https://prove2.me/submissions/ff5e6944-f729-46a6-b244-285883deada2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_holomorphic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hpos : 0<N) (τ : ℍ) :
    AnalyticAt ℂ ((lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex) (τ:ℂ) := by
  let U : Set ℂ := {z | 0<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ ((lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex) U := by
    intro z hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (lpsOriginalJDilated_holomorphic N hpos ⟨z,hz⟩)).differentiableWithinAt
  exact hf.analyticAt (hU.mem_nhds τ.im_pos)
end QEC.Coding.TannerLiftedProduct
