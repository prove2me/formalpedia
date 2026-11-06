-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleVanishingDivisors_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:33:25.96598+00:00
-- url     : https://prove2.me/submissions/8687b1d6-3013-4d59-96eb-8168f2b3de54

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono


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
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    {omega : GlobalAdeleWeilDifferential k F}
    {D E : Divisor (GlobalPlace k F)} (hED : E ≤ D)
    (hD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega) :
    E ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by
  intro a ha
  apply hD a
  exact (sup_le_sup
    (globalAdeleFilter_mono (k := k) (F := F) hED) le_rfl) ha
end QEC.Coding.AlgebraicGeometry.GlobalPlace
