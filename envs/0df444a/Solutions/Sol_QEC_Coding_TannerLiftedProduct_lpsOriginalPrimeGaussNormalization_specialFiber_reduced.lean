-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGaussNormalization_specialFiber_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:23:41.841451+00:00
-- url     : https://prove2.me/submissions/0fa37136-67d4-4b34-a7b7-030d821f1afe

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    letI : CommRing (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) := inferInstance
    letI : Ring (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) := CommRing.toRing
    letI : Semiring (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) :=
      (inferInstance : CommRing (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))).toCommSemiring.toSemiring
    IsReduced (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (integralClosure (LPSOriginalGaussBase p)
            (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p)
        (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p
  let D := integralClosure A (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)
  let : CommRing D := inferInstance
  let : Ring D := CommRing.toRing
  let : Semiring D := (inferInstance : CommRing D).toCommSemiring.toSemiring
  let m := IsLocalRing.maximalIdeal A
  let e : B ≃ₐ[A] D := lpsOriginalPrimeGaussNormalizationEquiv p
  have he : e.toRingHom.comp (algebraMap A B) = algebraMap A D := by
    apply RingHom.ext
    exact e.commutes
  have hi : m.map (algebraMap A D) =
      (m.map (algebraMap A B)).map e.toRingHom := by
    rw [Ideal.map_map,he]
  let q : B ⧸ m.map (algebraMap A B) ≃+* D ⧸ m.map (algebraMap A D) :=
    Ideal.quotientEquiv _ _ e.toRingEquiv hi
  let := lpsOriginalPrimeGaussAffineOrder_specialFiber_reduced p
  exact isReduced_of_injective q.symm q.symm.injective
end QEC.Coding.TannerLiftedProduct
