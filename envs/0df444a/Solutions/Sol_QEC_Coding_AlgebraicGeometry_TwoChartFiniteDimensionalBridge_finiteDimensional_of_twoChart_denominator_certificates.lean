-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:27.01435+00:00
-- url     : https://prove2.me/submissions/eac10cf3-306c-4dc3-9e19-c7a9a768f85a

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_directLaurentWindowCoordinates_finiteDimensional
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_scaled_coordinate_mem_directLaurentWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_scaled_coordinates_mem_windowCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_twoChartScaledCoordinateMap_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectChartCommonDenominator_exists_common_denominator_direct_chart
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_exists_inverse_chart_common_denominator_in_direct_laurent_coordinates


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution
    [Field k] [Field F] [Algebra k F]
    [ρ : Algebra (RatFunc k) F] [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F)
    (L : Submodule k F) (Λdirect : Submodule (Polynomial k) F)
    [Module.Finite (Polynomial k) Λdirect]
    (hdirectContains : ∀ x : L, (x : F) ∈ Λdirect)
    (hinverseContains :
      let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∃ Λinverse : Submodule (Polynomial k) F,
        Module.Finite (Polynomial k) Λinverse ∧
        ∀ x : L, (x : F) ∈ Λinverse) :
    FiniteDimensional k L := by
  obtain ⟨a, ha, hdirect⟩ :=
    _root_.QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator.exists_common_denominator_direct_chart
      (b := b) Λdirect
  let S : Polynomial k → F →ₗ[k] (ι →₀ RatFunc k) :=
    fun d => twoChartScaledCoordinateMap b a d
  have hSinjective : ∀ d : Polynomial k, d ≠ 0 → Function.Injective (S d) := by
    intro d hd
    simpa [S] using twoChartScaledCoordinateMap_injective b ha hd
  obtain ⟨d, hd, hinverseL⟩ : ∃ d : Polynomial k, d ≠ 0 ∧
      (let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : IsScalarTower (Polynomial k) (RatFunc k) F :=
        InverseAffinePlace.transportedScalarTower
          (k := k) (F := F) (oldRationalAlgebra := ρ)
      let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      ∀ x : L, ∀ j : ι, ∃ q : Polynomial k,
        InverseAffinePlace.rationalInvolution k
          ((InverseChartDenominatorTransport.inverseBasis
            (ρ := ρ) (_π := π) (_τ := τ) (φ := φ) (s := s) b).repr
              (d • (x : F)) j) =
            InverseChartDenominatorTransport.directLaurentToRatFunc k
              (InverseChartDenominatorTransport.inverseLaurentCoordinate k q)) := by
    let : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    let : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    let : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    rcases hinverseContains with ⟨Λinverse, hfiniteInverse, hcontainsInverse⟩
    let : Module.Finite (Polynomial k) Λinverse := hfiniteInverse
    obtain ⟨d, hd, hinverse⟩ :=
      InverseChartDenominatorTransport.exists_inverse_chart_common_denominator_in_direct_laurent_coordinates
          (ρ := ρ) (π := π) (τ := τ) (φ := φ) (s := s) (b := b) Λinverse hfiniteInverse
    refine ⟨d, hd, ?_⟩
    dsimp only
    intro x j
    exact hinverse ⟨x, hcontainsInverse x⟩ j
  let W := directLaurentWindowCoordinates k ι
    (-(d.natDegree : ℤ)) (a.natDegree : ℤ)
  have hS : ∀ x : L, S d x ∈ W := by
    intro x
    change twoChartScaledCoordinateMap b a d x ∈ W
    apply scaled_coordinates_mem_windowCoordinates
    intro j
    apply scaled_coordinate_mem_directLaurentWindow b a d (x : F) j
    · rcases hdirect ⟨x, hdirectContains x⟩ j with ⟨p, hp⟩
      exact ⟨p, hp.symm⟩
    · exact hinverseL x j
  let SL : L →ₗ[k] W :=
    ((S d).comp L.subtype).codRestrict W hS
  have hSL : Function.Injective SL := by
    intro x y hxy
    apply Subtype.ext
    apply hSinjective d hd
    exact congrArg Subtype.val hxy
  let : FiniteDimensional k W :=
    directLaurentWindowCoordinates_finiteDimensional (ι := ι) k
      (-(d.natDegree : ℤ)) (a.natDegree : ℤ)
  exact FiniteDimensional.of_injective (V₂ := W) SL hSL
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
