-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraUnitCommutatorNormOne_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:12:11.715636+00:00
-- url     : https://prove2.me/submissions/7f5da453-c592-4852-89cc-bc9a3e69fcc4

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

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (CyclicAlgebra P r)ˣ) :
    cyclicAlgebraNormOneToIndexLocal P r level
        (cyclicAlgebraUnitCommutatorNormOne P r u v) =
      indexLocalGLCommutatorToSL P r level
        (Units.map
          (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom u)
        (Units.map
          (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom v) := by
  rw [← cyclicAlgebraNormOneToIndexLocalNormOne_compatibility]
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hleft : Matrix.SpecialLinearGroup.toGL
      (indexLocalCyclicAlgebraNormOneEquivSL P r level
        (cyclicAlgebraNormOneToIndexLocalNormOne P r level
          (cyclicAlgebraUnitCommutatorNormOne P r u v))) =
      indexLocalCyclicAlgebraUnitEquivGL P r level
        (cyclicAlgebraUnitToIndexLocalCyclicAlgebra P r level ⁅u, v⁆) := by
    apply Units.ext
    rfl
  rw [hleft,
    indexLocalCyclicAlgebraUnitEquivGL_global_compatibility]
  apply Units.ext
  change cyclicAlgebraToIndexLocalMatrix P r level (↑⁅u, v⁆) =
    ↑⁅Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom u,
      Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom v⁆
  exact congrArg Units.val
    (map_commutatorElement
      (Units.map
        (cyclicAlgebraToIndexLocalMatrix P r level).toRingHom.toMonoidHom)
      u v)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
