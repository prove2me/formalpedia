-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJ_not_prime_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:04:44.191533+00:00
-- url     : https://prove2.me/submissions/95fdf0ef-7c56-4392-980f-ef06c1645f28

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueFractionMap_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_separable_overJ
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_separable_extension_not_prime_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionCoordinate_not_prime_power


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    u^p ≠ lpsOriginalGaussMaximalResidueJ N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p))) K :=
    lpsOriginalGaussMaximalResidue_separable_overJ N hN p hpN q
  have h := QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
    (FractionRing (Polynomial (ZMod p))) K p
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X)
    (lpsOriginalFractionCoordinate_not_prime_power (ZMod p) p (Fact.out : p.Prime)) u
  change u^p ≠ lpsOriginalGaussMaximalResidueFractionMap N hN p q
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) at h
  rw [lpsOriginalGaussMaximalResidueFractionMap_X] at h
  exact h
end QEC.Coding.TannerLiftedProduct
