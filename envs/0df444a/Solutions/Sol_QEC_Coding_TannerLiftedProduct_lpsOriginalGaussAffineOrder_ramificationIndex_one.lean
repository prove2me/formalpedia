-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_ramificationIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:23:52.38812+00:00
-- url     : https://prove2.me/submissions/8aa45887-9e35-4b93-8d39-5ad898662f90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsPrime] :
    q.ramificationIdx (LPSOriginalGaussBase p) = 1 := by
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  let : Algebra.FormallyUnramified (LPSOriginalGaussAffineOrder N hN p)
      (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  let : Algebra.IsUnramifiedAt (LPSOriginalGaussBase p) q :=
    Algebra.FormallyUnramified.comp (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p) (Localization.AtPrime q)
  exact Ideal.ramificationIdx_eq_one q (LPSOriginalGaussBase p)
end QEC.Coding.TannerLiftedProduct
