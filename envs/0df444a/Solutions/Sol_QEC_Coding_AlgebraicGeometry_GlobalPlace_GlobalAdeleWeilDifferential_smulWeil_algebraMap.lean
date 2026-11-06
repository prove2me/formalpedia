-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential.smulWeil_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:30:30.9662+00:00
-- url     : https://prove2.me/submissions/4b019667-b4c0-47ef-ab1e-0eb37ba12d1a

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
theorem _root_.solution (c : k)
    (omega : GlobalAdeleWeilDifferential k F)
    (a : GlobalAdele (k := k) (F := F)) :
    (smulWeil (algebraMap k F c) omega).toFun a = c • omega.toFun a := by
  rw [smulWeil_toFun_apply, algebraMap_smul, map_smul]
end QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential
