-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeBranchIdeals_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:35:49.826697+00:00
-- url     : https://prove2.me/submissions/fa721102-d9c7-4e42-a5a5-d056a3068f2f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSurjectiveProductKernels_coprime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    IsCoprime (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q)
      (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) :=
  lpsOriginalSurjectiveProductKernels_coprime _
    (lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q)
end QEC.Coding.TannerLiftedProduct
