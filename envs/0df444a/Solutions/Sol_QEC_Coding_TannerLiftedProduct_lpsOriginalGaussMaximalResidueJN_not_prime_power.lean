-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_not_prime_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:43.790032+00:00
-- url     : https://prove2.me/submissions/3cae0b73-ef65-4c4c-9382-b5f1e54c73f3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_FractionMap_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_separable_overJN
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionCoordinate_not_prime_power
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_separable_extension_not_prime_power


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    u^p ≠ lpsOriginalGaussMaximalResidueJN N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p))) K :=
    lpsOriginalGaussMaximalResidue_separable_overJN N hN p hpN q
  have h := QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
    (FractionRing (Polynomial (ZMod p))) K p
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X)
    (lpsOriginalFractionCoordinate_not_prime_power (ZMod p) p (Fact.out : p.Prime)) u
  change u^p ≠ lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) at h
  rw [lpsOriginalGaussMaximalResidueJN_FractionMap_X] at h
  exact h
end QEC.Coding.TannerLiftedProduct
