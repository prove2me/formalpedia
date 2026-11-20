-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_separable_overJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:51:56.575403+00:00
-- url     : https://prove2.me/submissions/0131a9c7-58e6-453d-9039-2b1726b2e00e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_actualResidueRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_separable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    IsSeparable (FractionRing (Polynomial (ZMod p)))
      (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  have hr := lpsOriginalModularPolynomialModFraction_actualResidueRoot N hN p q
  change Polynomial.aeval (lpsOriginalGaussMaximalResidueJN N hN p q)
    (lpsOriginalModularPolynomialModFraction N hN p) = 0 at hr
  exact (lpsOriginalModularPolynomialModFraction_separable N hN p hpN).of_dvd
    (minpoly.dvd _ _ hr)
end QEC.Coding.TannerLiftedProduct
