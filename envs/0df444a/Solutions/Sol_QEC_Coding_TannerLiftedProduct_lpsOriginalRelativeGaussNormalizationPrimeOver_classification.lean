-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationPrimeOver_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:48:04.194114+00:00
-- url     : https://prove2.me/submissions/c1eb24cc-f1c2-4d42-aca9-1dded7b9d1b7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckePrimeOver_classification


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Ideal (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)) [P.IsPrime]
    (hPq : P.comap (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) = q) :
    P = LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q ∨
      P = LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q := by
  let e := lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
  let P₀ := P.comap e
  let : P₀.IsPrime := Ideal.comap_isPrime e P
  let : P₀.LiesOver q := by
    constructor
    change q = (P.comap e).comap (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p))
    change q = P.comap (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    exact hPq.symm
  rcases lpsOriginalRelativeGaussHeckePrimeOver_classification N hN p hpN q P₀ with h | h
  · exact Or.inl ((P.map_comap_eq_self_of_equiv e).symm.trans
      (congrArg (fun I => I.map e) h))
  · exact Or.inr ((P.map_comap_eq_self_of_equiv e).symm.trans
      (congrArg (fun I => I.map e) h))
end QEC.Coding.TannerLiftedProduct
