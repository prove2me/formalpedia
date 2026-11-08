-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_specialFiber_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:24:02.428314+00:00
-- url     : https://prove2.me/submissions/572e7881-015c-414a-83e0-93472acdf34d

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
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Nontrivial (LPSOriginalGaussAffineOrder N hN p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))) := by
  let : Module.Free (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).free_adjoinRoot
  let : Module.Finite (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let := lpsOriginalGaussAffineOrder_domain N hN p
  obtain ⟨q,hq,hqover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := LPSOriginalGaussBase p) (S := LPSOriginalGaussAffineOrder N hN p)
    (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder N hN p))]
      exact bot_le)
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top hq.ne_top
    (Ideal.map_le_of_le_comap (le_of_eq hqover.symm))
end QEC.Coding.TannerLiftedProduct
