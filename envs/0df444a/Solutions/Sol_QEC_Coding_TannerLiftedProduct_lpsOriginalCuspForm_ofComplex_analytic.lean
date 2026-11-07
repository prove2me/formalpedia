-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForm_ofComplex_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:48:00.742458+00:00
-- url     : https://prove2.me/submissions/e2971910-3ee6-443f-b0d5-54889da7c216

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (τ : ℍ) :
    AnalyticAt ℂ ((f : ℍ→ℂ)∘UpperHalfPlane.ofComplex) (τ:ℂ) := by
  let U : Set ℂ := {z | 0<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hf : DifferentiableOn ℂ ((f : ℍ→ℂ)∘UpperHalfPlane.ofComplex) U := by
    intro z hz
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo f ⟨z,hz⟩)).differentiableWithinAt
  exact hf.analyticAt (hU.mem_nhds τ.im_pos)
end QEC.Coding.TannerLiftedProduct
