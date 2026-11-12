-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_orderIndexMatrixToCompleted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:46:05.751351+00:00
-- url     : https://prove2.me/submissions/89391739-023f-4ce9-bb69-e51b53195b9a

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

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
open scoped PowerSeries.WithPiTopology
variable (P : BasePrime) (r : Rank) (level : Nat)
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution :
    DenseRange (fun A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r) ↦
      A.map (indexCompletedArithmeticEval P r level)) := by
  intro M
  let A : Nat → Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ConstantArithmeticRing P r) :=
    fun n ↦ orderIndexMatrixFiniteJetLift P r level M n
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ (A n).map
      (indexCompletedArithmeticEval P r level))
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
