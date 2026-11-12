-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.denseRange_indexCompletedArithmeticEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:45:16.311512+00:00
-- url     : https://prove2.me/submissions/ca0c44e1-52da-48d9-b96f-441740a20513

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_indexCompletedArithmeticEval_finite_coeff_lift
section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
section CompletedTopology
open scoped PowerSeries.WithPiTopology
variable (P : BasePrime) (r : Rank) (level : Nat)
private theorem denseRange_powerSeries_of_finite_coeff_lifts
    {A K : Type*} [TopologicalSpace K] [CommSemiring K]
    (f : A → PowerSeries K)
    (hlift : ∀ (s : PowerSeries K) (n : Nat), ∃ a : A,
      ∀ k < n, PowerSeries.coeff k (f a) = PowerSeries.coeff k s) :
    DenseRange f := by
  intro s
  choose a ha using fun n ↦ hlift s n
  apply mem_closure_of_tendsto
    (f := fun n : Nat ↦ f (a n))
    (b := (Filter.atTop : Filter Nat))
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact tendsto_atTop_of_eventually_const fun n (hkn : k < n) ↦
      ha n k hkn
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_range_self (a n)
end CompletedTopology
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
open scoped PowerSeries.WithPiTopology
variable (P : BasePrime) (r : Rank) (level : Nat)
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFieldDiscreteTopology
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution :
    DenseRange (indexCompletedArithmeticEval P r level) :=
  denseRange_powerSeries_of_finite_coeff_lifts
    (indexCompletedArithmeticEval P r level)
    (exists_indexCompletedArithmeticEval_finite_coeff_lift P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
