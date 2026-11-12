-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_orderCyclicMatrixCoordinatesToCompleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:46:19.811003+00:00
-- url     : https://prove2.me/submissions/748ef139-dc2d-4805-bd95-2f695532c40e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexMatrixFiniteJetLift_to_global_mem_order

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
open scoped PowerSeries.WithPiTopology
variable (P : BasePrime) (r : Rank) (level : Nat)
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution :
    DenseRange (orderCyclicMatrixCoordinatesToCompleted P r level) := by
  intro M
  let A : Nat → OrderCyclicMatrixCoordinates P r := fun n ↦
    ⟨orderIndexMatrixFiniteJetLift P r level M n,
      orderIndexMatrixFiniteJetLift_to_global_mem_order P r level M n⟩
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ orderCyclicMatrixCoordinatesToCompleted
      P r level (A n))
    (b := (Filter.atTop : Filter Nat))
  · apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) ↦
      orderIndexMatrixFiniteJetLift_coeff P r level M n i j k hkn
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_range_self (A n)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
