-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranch_ramificationIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:47:34.141183+00:00
-- url     : https://prove2.me/submissions/4b188aa7-3a38-48cf-a653-7bec9dd21849

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeBranchIdeals_coprime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeBranchIdeals_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCoprimeMaximalIdeal_factorCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).ramificationIdx
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q _
    (lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot N p hNp h4N hN hpN q),
    AdjoinRoot.algebraMap_eq,← lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q,
    mul_comm]
  exact lpsOriginalCoprimeMaximalIdeal_factorCount _ _
    (lpsOriginalRelativeGaussHeckeBranchIdeals_coprime N hN p hpN q).symm
end QEC.Coding.TannerLiftedProduct
