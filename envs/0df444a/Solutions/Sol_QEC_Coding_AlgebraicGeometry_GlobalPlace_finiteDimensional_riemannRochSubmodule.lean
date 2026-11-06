-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:50:01.589277+00:00
-- url     : https://prove2.me/submissions/9e388c6a-1186-4af2-9002-d4001d2f981e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_mem_directChartFractionalLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRoch_mem_inverseChartFractionalLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_finiteDimensional_of_twoChart_denominator_certificates

section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
private theorem directChartModule_finite
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    Module.Finite (Polynomial k) (GlobalPlace.directChartModule (π := π) k F G) := by
  letI : Module.Finite (Polynomial k) (AffinePlace.affineRing k F) :=
    AffinePlace.finite_ringOfIntegers k F
  rw [Module.Finite.iff_fg]
  change ((AffinePlace.chartFractionalLattice k F
    (GlobalPlace.directChartDivisor (π := π) k F G)).coeToSubmodule.restrictScalars
      (Polynomial k)).FG
  exact (FractionalIdeal.fg_of_isNoetherianRing
    (S := (AffinePlace.affineRing k F)⁰) le_rfl
    (AffinePlace.chartFractionalLattice k F
      (GlobalPlace.directChartDivisor (π := π) k F G))).restrictScalars
private theorem inverseChartModule_finite
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    letI : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    Module.Finite (Polynomial k)
      (((AffinePlace.chartFractionalLattice k F
        (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G)).coeToSubmodule).restrictScalars
          (Polynomial k)) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  letI : Module.Finite (Polynomial k) (AffinePlace.affineRing k F) :=
    AffinePlace.finite_ringOfIntegers k F
  rw [Module.Finite.iff_fg]
  change (((AffinePlace.chartFractionalLattice k F
    (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G)).coeToSubmodule).restrictScalars
      (Polynomial k)).FG
  exact (FractionalIdeal.fg_of_isNoetherianRing
    (S := (AffinePlace.affineRing k F)⁰) le_rfl
    (AffinePlace.chartFractionalLattice k F
      (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G))).restrictScalars
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    : letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ G : Divisor (GlobalPlace k F),
      FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : IsScalarTower k (RatFunc k) F :=
    directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  intro G
  let b : Module.Basis (Fin (Module.finrank (RatFunc k) F)) (RatFunc k) F :=
    Module.finBasis (RatFunc k) F
  let Λdirect := GlobalPlace.directChartModule (π := π) k F G
  letI : Module.Finite (Polynomial k) Λdirect :=
    directChartModule_finite (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
  refine TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
      (ρ := ρ) (π := π) (τ := τ) (φ := φ) (s := s)
      (b := b) (L := GlobalPlace.riemannRochSubmodule G) Λdirect ?_ ?_
  · intro x
    exact GlobalPlace.riemannRoch_mem_directChartFractionalLattice
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G x
  · letI : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    let Λinverse := ((AffinePlace.chartFractionalLattice k F
      (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G)).coeToSubmodule).restrictScalars
        (Polynomial k)
    refine ⟨Λinverse, inverseChartModule_finite (π := π) (ρ := ρ)
      (τ := τ) (φ := φ) (s := s) k F G, ?_⟩
    intro x
    exact GlobalPlace.riemannRoch_mem_inverseChartFractionalLattice
      (π := π) (ρ := ρ) (φ := φ) (s := s) k F G x
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
