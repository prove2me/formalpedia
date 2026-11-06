-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.Rational.constantsToResidue_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:03:38.745953+00:00
-- url     : https://prove2.me/submissions/3a2aaea1-2e15-4af1-a85a-bf41fb23599b

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
open QEC.Coding.AlgebraicGeometry.AffinePlace.Rational
namespace QEC.Coding.AlgebraicGeometry.AffinePlace.Rational
theorem _root_.solution {P : carrier k F} (Q : Rational k F P) :
    Function.Bijective (constantsToResidue k F P) := by
  constructor
  · intro a b hab
    apply Q.constantsEquiv.injective
    simpa only [Q.constantsEquiv_apply] using hab
  · intro x
    obtain ⟨a, ha⟩ := Q.constantsEquiv.surjective x
    refine ⟨a, ?_⟩
    rw [← Q.constantsEquiv_apply a]
    exact ha
end QEC.Coding.AlgebraicGeometry.AffinePlace.Rational
