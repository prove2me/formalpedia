-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.residueCongruent_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:45:38.202202+00:00
-- url     : https://prove2.me/submissions/cde94db5-e284-4a9a-8129-ce46dddc44c8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (P : GlobalPlace k F) (omega : Differential k F) :
    ResidueCongruent P omega omega := by
  simp [ResidueCongruent, OrderAtLeast, localParameterPower]
end QEC.Coding.AlgebraicGeometry.Differential
