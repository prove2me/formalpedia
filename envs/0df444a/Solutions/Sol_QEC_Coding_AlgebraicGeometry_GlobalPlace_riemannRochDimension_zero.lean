-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:25:49.365884+00:00
-- url     : https://prove2.me/submissions/45f10072-c298-4f80-8374-f5fee36c016d

import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Constants

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial
open scoped Polynomial RatFunc WithZero nonZeroDivisors
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_39
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_42
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_45
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_48
open QEC.Coding.AlgebraicGeometry.GlobalPlace
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution [IsFullConstantField k F]
    [FiniteDimensional k (riemannRochSubmodule
      (0 : Divisor (GlobalPlace k F)))] :
    riemannRochDimension (0 : Divisor (GlobalPlace k F)) = 1 := by
  rw [riemannRochDimension,
    ← (constantsLinearEquivRiemannRochZero k F).finrank_eq]
  exact Module.finrank_self k
end QEC.Coding.AlgebraicGeometry.GlobalPlace
