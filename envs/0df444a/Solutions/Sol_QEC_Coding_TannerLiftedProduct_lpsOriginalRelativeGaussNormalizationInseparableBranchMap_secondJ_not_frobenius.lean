-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ_not_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:46:22.62043+00:00
-- url     : https://prove2.me/submissions/5671a8f4-b114-4671-9e7a-e1874e01e804

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRootPrimePower_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_not_prime_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_purelyInseparable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondLevelRoot


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) ≠
      (AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
        (lpsOriginalGaussMaximalResidueJ N hN p q))^p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let : IsPurelyInseparable K T :=
    lpsOriginalRelativeGaussInseparableBranch_purelyInseparable N hN p hpN q
  let f := lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
  let j := lpsOriginalGaussMaximalResidueJ N hN p q
  let jN := lpsOriginalGaussMaximalResidueJN N hN p q
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C jN
  let Y : T := AdjoinRoot.root Q
  intro heq
  have h := congrArg f
    (lpsOriginalRelativeGaussNormalization_secondLevelRoot N p hNp h4N hN hpN)
  rw [Polynomial.hom_eval₂,map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom T) (f
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)))
    (f (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)) = 0 at h
  rw [heq,lpsOriginalRelativeGaussNormalizationInseparableBranchMap_root] at h
  have hr : Polynomial.aeval Y
      ((lpsOriginalIntegerPolynomial N hN).map
        (Polynomial.eval₂RingHom (Int.castRingHom K) (j^p))) = 0 := by
    rw [Polynomial.aeval_def,Polynomial.eval₂_map,
      lpsOriginalBivariateIntegerCoefficientEval_comp_hom,map_pow]
    exact h
  have hs : IsSeparable K Y :=
    (lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable N hN p hpN q).of_dvd
      (minpoly.dvd K Y hr)
  obtain ⟨u,hu⟩ := IsPurelyInseparable.inseparable K Y hs
  have he : algebraMap K T (u^p) = algebraMap K T jN := by
    rw [map_pow,hu]
    exact lpsOriginalAdjoinRootPrimePower_root p jN
  exact lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q u
    ((algebraMap K T).injective he)
end QEC.Coding.TannerLiftedProduct
