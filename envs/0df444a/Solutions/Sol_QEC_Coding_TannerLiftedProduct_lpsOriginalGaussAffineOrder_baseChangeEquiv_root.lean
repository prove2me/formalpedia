-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_baseChangeEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:22:09.605004+00:00
-- url     : https://prove2.me/submissions/75aad72f-bb14-4cfb-a698-ddbbc6496aea

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
open scoped TensorProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    lpsOriginalGaussAffineOrder_baseChangeEquiv N hN p
      (1 ⊗ₜ[Polynomial ℤ] AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN)) =
    AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by
  exact QEC.Coding.AlgebraicGeometry.adjoinRoot_baseChangeEquiv_root
    (Polynomial ℤ) (LPSOriginalGaussBase p) (lpsOriginalIntegerPolynomial N hN)
end QEC.Coding.TannerLiftedProduct
