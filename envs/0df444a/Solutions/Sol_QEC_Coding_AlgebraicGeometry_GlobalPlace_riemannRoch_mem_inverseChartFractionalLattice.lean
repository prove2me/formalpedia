-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRoch_mem_inverseChartFractionalLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:53.981501+00:00
-- url     : https://prove2.me/submissions/ba288021-95ab-410d-a9b7-bd7b6f973018

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_inverseChartDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_mem_chartFractionalLattice_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_riemannRochSubmodule_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ (G : Divisor (GlobalPlace k F)) (x : GlobalPlace.riemannRochSubmodule G),
      letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      (x : F) ∈ AffinePlace.chartFractionalLattice k F
        (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  intro G x
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  rw [AffinePlace.mem_chartFractionalLattice_iff]
  intro P
  have hx := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp x.property
  calc
    AffinePlace.valuation k F P (x : F) =
        (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ) (φ := φ) (s := s) k F P).valuation
          (x : F) := rfl
    _ ≤ WithZero.exp (G (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ)
        (φ := φ) (s := s) k F P)) :=
      hx (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ) (φ := φ) (s := s) k F P)
    _ = WithZero.exp (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ)
        (φ := φ) (s := s) k F G P) := by
      rw [GlobalPlace.inverseChartDivisor_apply (π := π) (ρ := ρ) (φ := φ) (s := s)]
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
