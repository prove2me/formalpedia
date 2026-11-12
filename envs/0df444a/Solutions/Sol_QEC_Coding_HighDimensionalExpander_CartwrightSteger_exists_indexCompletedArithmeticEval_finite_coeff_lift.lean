-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_indexCompletedArithmeticEval_finite_coeff_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:13:08.6322+00:00
-- url     : https://prove2.me/submissions/34ea9dac-62dc-42da-9956-15f6dc32071f

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_indexCompletedPolynomialEval_finite_coeff_lift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : PowerSeries (ResidueField P r level)) (n : Nat) :
    ∃ a : ConstantArithmeticRing P r, ∀ k < n,
      PowerSeries.coeff k (indexCompletedArithmeticEval P r level a) =
        PowerSeries.coeff k s := by
  obtain ⟨f, hf⟩ :=
    exists_indexCompletedPolynomialEval_finite_coeff_lift P r level s n
  refine ⟨algebraMap (ConstantPolynomialRing P r)
    (ConstantArithmeticRing P r) f, ?_⟩
  intro k hk
  rw [indexCompletedArithmeticEval_algebraMap]
  exact hf k hk
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
