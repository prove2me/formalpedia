-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:13.860855+00:00
-- url     : https://prove2.me/submissions/11d3f2e6-ecab-45f5-b81c-de208ccbc02d

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_GlobalAdeleWeilDifferential_smulWeil_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe

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
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (E : Divisor (GlobalPlace k F)) (homega : omega.toFun ≠ 0) :
    Function.Injective
      (globalAdeleSmulIntoDifferentialSpace
        (k := k) (F := F) omega hD₀ E) := by
  intro f g hfg
  by_contra hne
  have hdifference : globalAdeleSmulIntoDifferentialSpace
      (k := k) (F := F) omega hD₀ E (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hvalue : (((f - g : riemannRochSubmodule E) : F)) ≠ 0 := by
    intro hzero
    exact hne (sub_eq_zero.mp (Subtype.ext hzero))
  have htoFun :
      (GlobalAdeleWeilDifferential.smulWeil
        ((f - g : riemannRochSubmodule E) : F) omega).toFun = 0 :=
    congrArg Subtype.val hdifference
  have hzero : GlobalAdeleWeilDifferential.smulWeil
      ((f - g : riemannRochSubmodule E) : F) omega = 0 :=
    GlobalAdeleWeilDifferential.ext htoFun
  have homegaZero :=
    (GlobalAdeleWeilDifferential.smulWeil_eq_zero_iff
      ((f - g : riemannRochSubmodule E) : F) hvalue omega).mp hzero
  apply homega
  rw [homegaZero]
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
