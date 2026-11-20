-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_actualResidueDualRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:49:40.814769+00:00
-- url     : https://prove2.me/submissions/1f3b9033-56f0-46c7-961a-3254df519d2b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalModularPolynomialModFraction N hN p).eval₂
      (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q)
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.eval₂_map,
    lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient]
  exact lpsOriginalIntegerPolynomial_gaussMaximalResidueDualRoot N hN p hpN q
end QEC.Coding.TannerLiftedProduct
