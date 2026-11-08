-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGaussNormalizationEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:23:22.004926+00:00
-- url     : https://prove2.me/submissions/97e3d9a8-494d-4261-b23c-5e932fe76324

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_root


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    ((lpsOriginalPrimeGaussNormalizationEquiv p
      (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))).val.val) =
      lpsOriginalJNInFractionField p (Fact.out : p.Prime).pos := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := .of_algebraMap_eq' rfl
  let := lpsOriginalPrimeGaussAffineOrder_isIntegralClosure p
  have he := IsIntegralClosure.algebraMap_equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))
    (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))
  change (lpsOriginalPrimeGaussNormalizationEquiv p
    (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))).val = _ at he
  exact (congrArg Subtype.val he).trans (lpsOriginalGaussAffineToGenerated_root p (Fact.out : p.Prime).pos p)
end QEC.Coding.TannerLiftedProduct
