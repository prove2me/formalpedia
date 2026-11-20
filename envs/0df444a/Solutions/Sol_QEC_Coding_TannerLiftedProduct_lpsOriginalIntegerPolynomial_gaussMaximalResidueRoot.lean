-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:38:30.753622+00:00
-- url     : https://prove2.me/submissions/9c65c6cd-8f34-466b-b5bc-46ebbc225550

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerBaseEval


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q))
      (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 := by
  have h := congrArg (Ideal.Quotient.mk q)
    (AdjoinRoot.eval₂_root (lpsOriginalGaussPolynomial N hN p))
  rw [Polynomial.hom_eval₂,map_zero] at h
  change ((lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).eval₂
    ((Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)))
    (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 at h
  rw [Polynomial.eval₂_map] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (((Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)))
    (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 at h
  rw [lpsOriginalGaussMaximalResidue_integerBaseEval] at h
  exact h
end QEC.Coding.TannerLiftedProduct
