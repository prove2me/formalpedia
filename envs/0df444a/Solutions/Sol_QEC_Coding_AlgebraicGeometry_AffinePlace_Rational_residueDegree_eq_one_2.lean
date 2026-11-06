-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.AffinePlace.Rational.residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:47:07.444411+00:00
-- url     : https://prove2.me/submissions/4a75a99e-df2f-4835-88a7-0affd82b4691

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_constantsToResidue_bijective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residueAlgebra_algebraMap


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
    residueDegree k F P = 1 := by
  unfold residueDegree
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : FiniteDimensional k (residueField k F P) :=
    residueField_finiteDimensional k F P
  apply Module.finrank_of_bijective_algebraMap
  rw [residueAlgebra_algebraMap k F P]
  exact Q.constantsToResidue_bijective
end QEC.Coding.AlgebraicGeometry.AffinePlace.Rational
