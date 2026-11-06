-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential.smulWeil_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:32:35.533279+00:00
-- url     : https://prove2.me/submissions/9ffe85a8-dc18-4e0d-a16e-6ad65a0d52a4

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleWeilAlgebra
attribute [local instance] globalAdeleWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleWeilScalarTower
attribute [local instance] globalAdeleWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilRiemannRochFiniteDimensional
attribute [local instance] globalAdeleWeilRiemannRochFiniteDimensional
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialSpaceFinite
attribute [local instance] globalAdeleDifferentialSpaceFinite
open QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential
variable {k F}
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential
theorem _root_.solution (x : F) (hx : x ≠ 0)
    (omega : GlobalAdeleWeilDifferential k F) :
    smulWeil x omega = 0 ↔ omega = 0 := by
  constructor
  · intro hxomega
    calc
      omega = (1 : F) • omega := (one_smul F omega).symm
      _ = (x⁻¹ * x) • omega := by rw [inv_mul_cancel₀ hx]
      _ = x⁻¹ • (x • omega) := mul_smul x⁻¹ x omega
      _ = x⁻¹ • smulWeil x omega := rfl
      _ = x⁻¹ • (0 : GlobalAdeleWeilDifferential k F) := by rw [hxomega]
      _ = 0 := smul_zero x⁻¹
  · intro homega
    subst omega
    exact smul_zero x
end QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential
