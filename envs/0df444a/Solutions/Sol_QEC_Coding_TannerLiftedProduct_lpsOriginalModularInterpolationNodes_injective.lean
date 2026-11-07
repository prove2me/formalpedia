-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularInterpolationNodes_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:53:39.276737+00:00
-- url     : https://prove2.me/submissions/51f5834d-84a8-4163-9f85-695e6b90c563

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (r : ℕ) :
    Function.Injective (fun i : Fin (r+1) => (i.val:ℂ)) := by
  intro i j h
  apply Fin.ext
  change (i.val:ℂ)=(j.val:ℂ) at h
  exact_mod_cast h
end QEC.Coding.TannerLiftedProduct
