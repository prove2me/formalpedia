-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_originalEval_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:22:08.12839+00:00
-- url     : https://prove2.me/submissions/acb01669-99dd-43ba-bc24-31b89b819bf1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalGaussPrime_isPrime
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalGaussPrime_principal
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalGaussAffineOrder_originalEval N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih q =>
    rw [lpsOriginalGaussAffineOrder_originalEval,AdjoinRoot.lift_mk] at hx
    apply AdjoinRoot.mk_eq_zero.mpr
    have hm : (lpsOriginalGaussPolynomial N hN p).Monic :=
      (lpsOriginalIntegerPolynomial_monic N hN).map _
    rw [← Polynomial.map_dvd_map (lpsOriginalGaussBaseFractionMap p)
      (lpsOriginalGaussBaseFractionMap_injective p)
      hm,
      lpsOriginalGaussPolynomial_fractionDiagram,
      lpsOriginalIntegerPolynomial_minpoly N hN,minpoly.dvd_iff]
    rw [Polynomial.aeval_def,Polynomial.eval₂_map]
    change q.eval₂ (lpsOriginalJFractionEmbeddingQ.comp
      (lpsOriginalGaussBaseFractionMap p)) (lpsOriginalJNInFractionField N hN) = 0
    exact hx
end QEC.Coding.TannerLiftedProduct
