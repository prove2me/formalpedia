-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_branchRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:02:20.672366+00:00
-- url     : https://prove2.me/submissions/6aae0a66-8ddd-44fc-b40e-b6dfd9de2b94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_integralSL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchSL_function

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalPrimeBranch p i τ)=0 := by
  have h:=lpsOriginalIntegerPolynomial_root p (Fact.out : p.Prime).pos
    (lpsOriginalPrimeBranchSL p i • τ)
  rw [lpsOriginalJInvariant_integralSL,lpsOriginalPrimeBranchSL_function] at h
  exact h
end QEC.Coding.TannerLiftedProduct
