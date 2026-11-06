-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:32:23.505096+00:00
-- url     : https://prove2.me/submissions/4576c5fb-9f22-4e50-928d-4b63571178c1

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleQuotientRank_eq_indexOfSpecialty


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
    (D : Divisor (GlobalPlace k F)) :
    Module.finrank k (globalAdeleDifferentialSpace (k := k) (F := F) D) =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
  let S := globalAdeleFilterAddDiagonal (k := k) (F := F) D
  have hspace : globalAdeleDifferentialSpace (k := k) (F := F) D =
      S.dualAnnihilator :=
    globalAdeleDifferentialSpace_eq_dualAnnihilator
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  rw [hspace, ← S.dualQuotEquivDualAnnihilator.finrank_eq,
    Subspace.dual_finrank_eq]
  exact globalAdeleQuotientRank_eq_indexOfSpecialty
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
end QEC.Coding.AlgebraicGeometry.GlobalPlace
