-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_globalAdeleFilter_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:18:47.245498+00:00
-- url     : https://prove2.me/submissions/fb325c52-e681-4b75-a8da-20acbfa3e1c0

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
section
namespace QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterModule
private theorem mem_globalAdeleFilter_divisorOfGlobalAdele
    (a : GlobalAdele (k := k) (F := F)) :
    a ∈ globalAdeleFilter (k := k) (F := F)
      (divisorOfGlobalAdele (k := k) (F := F) a) := by
  intro P
  show P.valuation (a.val P) ≤
    WithZero.exp (divisorOfGlobalAdele (k := k) (F := F) a P)
  change P.valuation (a.val P) ≤ WithZero.exp
    (if 1 < P.valuation (a.val P) then
      WithZero.log (P.valuation (a.val P)) else 0)
  by_cases hP : P.valuation (a.val P) ≤ 1
  · have hnotlt : ¬1 < P.valuation (a.val P) := not_lt.mpr hP
    rw [if_neg hnotlt, WithZero.exp_zero]
    exact hP
  · have hlt : 1 < P.valuation (a.val P) := not_le.mp hP
    have hval : P.valuation (a.val P) ≠ 0 :=
      ne_of_gt (zero_lt_one.trans hlt)
    rw [if_pos hlt, WithZero.exp_log hval]
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichScalarTower
attribute [local instance] globalAdeleSandwichScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterModule
attribute [local instance] globalAdeleSandwichFilterModule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (a : GlobalAdele (k := k) (F := F)) :
    ∃ D : Divisor (GlobalPlace k F),
      a ∈ globalAdeleFilter (k := k) (F := F) D :=
  ⟨divisorOfGlobalAdele (k := k) (F := F) a,
    mem_globalAdeleFilter_divisorOfGlobalAdele (k := k) (F := F) a⟩
end QEC.Coding.AlgebraicGeometry.GlobalPlace
