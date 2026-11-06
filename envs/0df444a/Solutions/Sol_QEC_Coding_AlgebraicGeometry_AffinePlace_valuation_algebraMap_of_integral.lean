-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.valuation_algebraMap_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:19:56.760444+00:00
-- url     : https://prove2.me/submissions/d453ff7e-3490-4279-ae13-531661ab171e

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
    valuation k F P
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
      P.intValuation x :=
  P.valuation_of_algebraMap (K := F) x
end QEC.Coding.AlgebraicGeometry.AffinePlace
