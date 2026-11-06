-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.Rational.residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:34:24.799977+00:00
-- url     : https://prove2.me/submissions/f6e234c6-bb0e-4ed4-bed4-e9f42f488b30

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
open QEC.Coding.AlgebraicGeometry.AffinePlace.Rational

theorem solution {P : carrier k F} (Q : Rational k F P) :
    residueDegree k F P = 1 := by
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  change Module.finrank k (residueField k F P) = 1
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
  have h : algebraMap k (residueField k F P) = Q.constantsEquiv.toRingHom := by
    ext a
    exact (Q.constantsEquiv_apply a).symm
  rw [h]
  exact Q.constantsEquiv.bijective
