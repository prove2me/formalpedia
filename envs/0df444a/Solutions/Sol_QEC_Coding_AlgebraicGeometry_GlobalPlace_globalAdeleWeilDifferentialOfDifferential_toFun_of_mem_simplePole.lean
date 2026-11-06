-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:48:24.989891+00:00
-- url     : https://prove2.me/submissions/d2ff861d-389b-4833-a614-b950a15ffad7

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
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : GlobalAdele (k := k) (F := F))
    (ha : a ∈ globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    (globalAdeleWeilDifferentialOfDifferential
      (k := k) (F := F) omega homega).toFun a =
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨a, ha⟩ :=
  differentialResidueExtension_apply_of_mem_simplePole
    (k := k) (F := F) omega homega a ha
end QEC.Coding.AlgebraicGeometry.GlobalPlace
