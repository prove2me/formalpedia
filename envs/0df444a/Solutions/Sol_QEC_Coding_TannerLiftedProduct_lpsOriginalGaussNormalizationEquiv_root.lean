-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussNormalizationEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:40:40.607942+00:00
-- url     : https://prove2.me/submissions/1bdbc55a-9ed9-4b89-bf5c-435ab54fe006

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_root

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalGaussPrime_isPrime
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalGaussPrime_principal
open scoped TensorProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    ((lpsOriginalGaussNormalizationEquiv N hN p hpN
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val) =
      lpsOriginalJNInFractionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let := lpsOriginalGaussAffineOrder_isIntegralClosure N hN p hpN
  have he := IsIntegralClosure.algebraMap_equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder N hN p) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN))
    (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))
  change (lpsOriginalGaussNormalizationEquiv N hN p hpN
    (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val = _ at he
  exact (congrArg Subtype.val he).trans (lpsOriginalGaussAffineToGenerated_root N hN p)
end QEC.Coding.TannerLiftedProduct
