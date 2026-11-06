-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.valuation_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:04:31.581723+00:00
-- url     : https://prove2.me/submissions/2c5c45fc-7b8f-4bda-8735-1b5dd440e8f7

import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace

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
theorem _root_.solution (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    valuation k F P x = P.intValuation x :=
  P.valuation_of_algebraMap (K := F) x
end QEC.Coding.AlgebraicGeometry.AffinePlace
