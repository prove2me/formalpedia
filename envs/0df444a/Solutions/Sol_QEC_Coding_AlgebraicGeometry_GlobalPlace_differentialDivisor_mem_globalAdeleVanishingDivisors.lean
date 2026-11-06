-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.differentialDivisor_mem_globalAdeleVanishingDivisors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:48:52.583432+00:00
-- url     : https://prove2.me/submissions/b55dc0a9-24b9-407c-a31c-585dc2372ff3

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilAlgebra
attribute [local instance] globalAdeleDifferentialWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilScalarTower
attribute [local instance] globalAdeleDifferentialWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0) :
    FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega ∈
      globalAdeleVanishingDivisors (k := k) (F := F)
        (globalAdeleWeilDifferentialOfDifferential
          (k := k) (F := F) omega homega) :=
  differentialResidueExtension_vanishes
    (k := k) (F := F) omega homega
end QEC.Coding.AlgebraicGeometry.GlobalPlace
