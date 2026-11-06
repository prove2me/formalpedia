-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.divisorDegree_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:21.356585+00:00
-- url     : https://prove2.me/submissions/ac6128c6-ad8a-4834-9c5e-387c20457f05

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
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
theorem solution (D : Divisor (carrier k F)) :
    divisorDegree k F D = Divisor.degree (residueDegree k F) D := by
  rfl
