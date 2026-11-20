-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_FractionMap_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:36:10.178779+00:00
-- url     : https://prove2.me/submissions/d4bae480-8b03-4e07-bf17-24ff9980fea2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionLift_polynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).comp
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))) =
      Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  exact lpsOriginalFractionLift_polynomial (ZMod p)
    (LPSOriginalGaussAffineOrder N hN p ⧸ q)
    (Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q))
    (transcendental_iff_injective.mp
      (lpsOriginalGaussMaximalResidueJN_transcendental N hN p hpN q))
end QEC.Coding.TannerLiftedProduct
