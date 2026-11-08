-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerAffineRing_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:13:53.008738+00:00
-- url     : https://prove2.me/submissions/0d7312e2-1b88-4230-bcc3-56093d5931a6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    Module.finrank (Polynomial ℤ) (lpsOriginalIntegerAffineRing N hN)=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  change Module.finrank (Polynomial ℤ) (AdjoinRoot (lpsOriginalIntegerPolynomial N hN))=_
  exact (AdjoinRoot.isAdjoinRootMonic _
    (lpsOriginalIntegerPolynomial_monic N hN)).finrank.trans
      (lpsOriginalIntegerPolynomial_degree N hN)
end QEC.Coding.TannerLiftedProduct
