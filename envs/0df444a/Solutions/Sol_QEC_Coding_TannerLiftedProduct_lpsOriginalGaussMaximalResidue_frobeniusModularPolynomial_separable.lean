-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:39:08.878442+00:00
-- url     : https://prove2.me/submissions/b3723e0b-9f4b-4e04-bd07-57bcf3fcdade

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_separable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    ((lpsOriginalIntegerPolynomial N hN).map
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        ((lpsOriginalGaussMaximalResidueJ N hN p q)^p))).Separable := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  have h := (lpsOriginalModularPolynomialModFraction_separable N hN p hpN).map
    (f := lpsOriginalGaussMaximalResidueFractionMap N hN p q)
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.map_map,
    lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient] at h
  have hf := h.map (f := frobenius K p)
  rw [Polynomial.map_map,lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at hf
  exact hf
end QEC.Coding.TannerLiftedProduct
