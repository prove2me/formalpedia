-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJ_separable_overJN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:00:40.7957+00:00
-- url     : https://prove2.me/submissions/974790b4-f4ba-40b1-937a-ed86925f0ac8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_actualResidueDualRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_separable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
    IsSeparable (FractionRing (Polynomial (ZMod p)))
      (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  have hr := lpsOriginalModularPolynomialModFraction_actualResidueDualRoot N hN p hpN q
  change Polynomial.aeval (lpsOriginalGaussMaximalResidueJ N hN p q)
    (lpsOriginalModularPolynomialModFraction N hN p) = 0 at hr
  exact (lpsOriginalModularPolynomialModFraction_separable N hN p hpN).of_dvd
    (minpoly.dvd _ _ hr)
end QEC.Coding.TannerLiftedProduct
