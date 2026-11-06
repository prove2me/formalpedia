-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differential_ne_zero_iff_functionFieldDerivation_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:55.290198+00:00
-- url     : https://prove2.me/submissions/d0d06a8e-2dff-4726-841d-1e00056bf26b

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (f : F) :
    differential k F f ≠ 0 ↔ functionFieldDerivation (k := k) (F := F) f ≠ 0 := by
  constructor
  · intro hdifferential hderivation
    apply hdifferential
    rw [differential_eq_functionFieldDerivation_smul_generator, hderivation, zero_smul]
  · intro hderivation hdifferential
    have hsmul : functionFieldDerivation (k := k) (F := F) f •
        functionFieldDifferentialGenerator (k := k) (F := F) = 0 := by
      rw [← differential_eq_functionFieldDerivation_smul_generator]
      exact hdifferential
    rcases smul_eq_zero.mp hsmul with hvalue | hgenerator
    · exact hderivation hvalue
    · exact functionFieldDifferentialGenerator_ne_zero (k := k) (F := F) hgenerator
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
