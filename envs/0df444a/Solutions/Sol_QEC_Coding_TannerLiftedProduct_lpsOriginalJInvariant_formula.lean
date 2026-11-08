-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:04:38.614122+00:00
-- url     : https://prove2.me/submissions/7517055d-19fe-4b02-8bae-dff59e3da037

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (τ : ℍ) :
    lpsOriginalJInvariant τ=
      1728*ModularForm.E₄ τ^3/(ModularForm.E₄ τ^3-ModularForm.E₆ τ^2) := by
  rw [lpsOriginalJInvariant,ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  rw [div_div_eq_mul_div]
  ring
end QEC.Coding.TannerLiftedProduct
