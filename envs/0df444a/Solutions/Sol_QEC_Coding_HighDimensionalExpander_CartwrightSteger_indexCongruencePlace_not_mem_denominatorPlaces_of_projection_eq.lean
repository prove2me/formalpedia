-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:13:29.100655+00:00
-- url     : https://prove2.me/submissions/aec85163-e748-49d0-b37e-dc0ad6cd8cfe

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (hproj : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u =
      arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level v)
    (hv : (v : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
          ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
        (↑v⁻¹ : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
          ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    indexCongruencePlace P r level ∉
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u := by
  have hadic_of_projection_eq
      (a b : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
      (hab : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level a =
        arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level b) :
      arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
          (a : ArithmeticFiniteAdeleCyclicAlgebra P r) =
        arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace P r level
          (b : ArithmeticFiniteAdeleCyclicAlgebra P r) := by
    apply (indexAdicCyclicAlgebraToIndexLocalCyclicAlgebra_bijective
      P r level).1
    exact congrArg Units.val hab
  have hcoord_of_projection_eq
      (a b : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
      (hab : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level a =
        arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level b)
      (p : Fin r.matrixRank × Fin r.matrixRank) :
      arithmeticFiniteAdeleAtIndexPlace P r level
          ((arithmeticFiniteAdeleCyclicBasis P r).equivFun a p) =
        arithmeticFiniteAdeleAtIndexPlace P r level
          ((arithmeticFiniteAdeleCyclicBasis P r).equivFun b p) := by
    calc
      _ = (indexAdicCyclicBasis P r level).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
            P r level (a : ArithmeticFiniteAdeleCyclicAlgebra P r)) p :=
        (indexAdicCyclicBasis_equivFun_atIndexPlace
          P r level (a : ArithmeticFiniteAdeleCyclicAlgebra P r) p).symm
      _ = (indexAdicCyclicBasis P r level).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtIndexPlace
            P r level (b : ArithmeticFiniteAdeleCyclicAlgebra P r)) p :=
        congrArg (fun x =>
          (indexAdicCyclicBasis P r level).equivFun x p)
          (hadic_of_projection_eq a b hab)
      _ = _ := indexAdicCyclicBasis_equivFun_atIndexPlace
        P r level (b : ArithmeticFiniteAdeleCyclicAlgebra P r) p
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces, Set.mem_union]
  push Not
  constructor
  · intro hu
    obtain ⟨p, hp⟩ := hu
    apply hp
    change arithmeticFiniteAdeleAtIndexPlace P r level
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun u p) ∈
        (indexCongruencePlace P r level).adicCompletionIntegers
          (FunctionField P)
    rw [hcoord_of_projection_eq u v hproj p]
    exact hv.1 p (indexCongruencePlace P r level)
  · intro huInv
    obtain ⟨p, hp⟩ := huInv
    apply hp
    have hprojInv :
        arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u⁻¹ =
          arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level v⁻¹ := by
      rw [map_inv, map_inv, hproj]
    change arithmeticFiniteAdeleAtIndexPlace P r level
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun (↑u⁻¹) p) ∈
        (indexCongruencePlace P r level).adicCompletionIntegers
          (FunctionField P)
    rw [hcoord_of_projection_eq u⁻¹ v⁻¹ hprojInv p]
    exact hv.2 p (indexCongruencePlace P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
