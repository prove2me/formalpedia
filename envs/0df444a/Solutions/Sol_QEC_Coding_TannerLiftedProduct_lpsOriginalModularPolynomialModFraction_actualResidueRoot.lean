-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_actualResidueRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:44:28.443424+00:00
-- url     : https://prove2.me/submissions/7620c749-fd94-482c-b591-dd4bfa4f1b05

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalModularPolynomialModFraction N hN p).eval₂
      (lpsOriginalGaussMaximalResidueFractionMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 := by
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.eval₂_map,
    lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient]
  exact lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot N hN p q
end QEC.Coding.TannerLiftedProduct
