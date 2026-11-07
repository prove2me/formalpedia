-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_etale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:31:32.759748+00:00
-- url     : https://prove2.me/submissions/547f2419-51d2-444f-b459-706cd36df70f

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
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    Algebra.Etale (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) := by
  let : Module.Free (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).free_adjoinRoot
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  exact Algebra.Etale.of_formallyUnramified_of_flat
end QEC.Coding.TannerLiftedProduct
