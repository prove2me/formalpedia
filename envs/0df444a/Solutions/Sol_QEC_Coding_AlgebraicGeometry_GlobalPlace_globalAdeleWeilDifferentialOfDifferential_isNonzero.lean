-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferentialOfDifferential_isNonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:52:37.267995+00:00
-- url     : https://prove2.me/submissions/1d493c87-7800-4cec-87bf-3341265cf725

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_infinityFibre_nonempty

section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] globalAdeleDifferentialWeilAlgebra
attribute [local instance] globalAdeleDifferentialWeilScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
private theorem globalPlace_nonempty : Nonempty (GlobalPlace k F) := by
  obtain ⟨D⟩ := InverseAffinePlace.infinityFibre_nonempty
    (oldRationalAlgebra := ρ) k F
  exact ⟨InverseAffinePlace.infinityFibreGlobalPlace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s) D⟩
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

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
    GlobalAdeleWeilDifferential.IsNonzero
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega) := by
  let P := Classical.choice
    (globalPlace_nonempty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  obtain ⟨a, ha⟩ :=
    globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
      (k := k) (F := F) omega homega P (1 : k)
  intro hzero
  have hvalue :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 1 := by
    rw [globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
      (k := k) (F := F) omega homega _
      (globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega P a.property)]
    exact ha
  have hvalueZero :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 0 := by
    rw [hzero]
    exact LinearMap.zero_apply _
  exact one_ne_zero (hvalue.symm.trans hvalueZero)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
