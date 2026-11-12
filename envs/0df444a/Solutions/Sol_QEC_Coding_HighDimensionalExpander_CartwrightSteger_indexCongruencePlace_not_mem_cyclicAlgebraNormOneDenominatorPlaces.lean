-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruencePlace_not_mem_cyclicAlgebraNormOneDenominatorPlaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:27:01.244201+00:00
-- url     : https://prove2.me/submissions/6a7543f5-277b-49c3-a90c-92b2f2cb9d92

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraNormOneToIndexLocalNormOne_compatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_indexCompletedNormOne_of_mem_finiteTargetNeighborhood
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (u : CyclicAlgebraNormOne P r)
    (hu : cyclicAlgebraNormOneToIndexLocal P r level u ∈
      indexLocalNormOneFiniteTargetNeighborhood P r level g) :
    indexCongruencePlace P r level ∉
      cyclicAlgebraNormOneDenominatorPlaces P r u := by
  obtain ⟨t, htlocal, _⟩ :=
    exists_indexCompletedNormOne_of_mem_finiteTargetNeighborhood
      P r level g (cyclicAlgebraNormOneToIndexLocal P r level u) hu
  let a : ArithmeticFiniteAdeleCyclicNormOne P r :=
    cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r u
  let b : ArithmeticFiniteAdeleCyclicNormOne P r :=
    indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
      P r level t
  have hprojNorm :
      arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level a =
        arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level b := by
    apply (indexLocalCyclicAlgebraNormOneEquivSL P r level).injective
    calc
      indexLocalCyclicAlgebraNormOneEquivSL P r level
          (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level a) =
        cyclicAlgebraNormOneToIndexLocal P r level u := by
          rw [show a = cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne
              P r u from rfl,
            arithmeticFiniteAdeleNormOneToIndexLocalNormOne_diagonal,
            cyclicAlgebraNormOneToIndexLocalNormOne_compatibility]
      _ = indexCompletedNormOneInnerFormToIndexLocal P r level t :=
        htlocal.symm
      _ = indexLocalCyclicAlgebraNormOneEquivSL P r level
          (arithmeticFiniteAdeleNormOneToIndexLocalNormOne P r level b) := by
        rw [show b =
            indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne
              P r level t from rfl]
        exact
          (indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_projection
            P r level t).symm
  change indexCongruencePlace P r level ∉
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r a.1
  apply indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
    P r level a.1 b.1
  · exact congrArg Subtype.val hprojNorm
  · exact indexCompletedNormOneInnerFormToArithmeticFiniteAdeleNormOne_integral
      P r level t
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
