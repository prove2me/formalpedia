-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.residue_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:18:45.675437+00:00
-- url     : https://prove2.me/submissions/0f3d4ad7-618f-483e-b7cf-648d400481d3

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
    residue k F P x = 0 ↔ x ∈ P.asIdeal := by
  change algebraMap (_root_.FunctionField.ringOfIntegers k F) P.asIdeal.ResidueField x = 0 ↔
    x ∈ P.asIdeal
  exact
    (Ideal.algebraMap_residueField_eq_zero
      (R := _root_.FunctionField.ringOfIntegers k F) (I := P.asIdeal) (x := x))
end QEC.Coding.AlgebraicGeometry.AffinePlace
