-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.divisorDegree_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:06.271864+00:00
-- url     : https://prove2.me/submissions/64b0c21d-d298-447b-9877-f476fbd1fd1c

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add


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
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (D E : Divisor (carrier k F)) :
    divisorDegree k F (D + E) = divisorDegree k F D + divisorDegree k F E :=
  Divisor.degree_add (residueDegree k F) D E
end QEC.Coding.AlgebraicGeometry.AffinePlace
