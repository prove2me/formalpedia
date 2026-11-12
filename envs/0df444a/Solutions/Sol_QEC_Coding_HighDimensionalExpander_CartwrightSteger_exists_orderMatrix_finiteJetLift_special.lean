-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_orderMatrix_finiteJetLift_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:44:37.030189+00:00
-- url     : https://prove2.me/submissions/8cb7da5f-7eef-4e7e-9ed1-ba5f63c0e8de

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
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    ∃ A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ConstantArithmeticRing P r),
      A.map (constantArithmeticToSplittingFunctionField P r) ∈
          CartwrightStegerOrder P r ∧
      (∀ (i j : Fin r.matrixRank) (k : Nat), k < n →
        PowerSeries.coeff k
            ((A.map (indexCompletedArithmeticEval P r level)) i j) =
          PowerSeries.coeff k
            (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) :
              Matrix (Fin r.matrixRank) (Fin r.matrixRank)
                (PowerSeries (ResidueField P r level))) i j)) ∧
      (∀ k : Nat, k < n →
        PowerSeries.coeff k
            (Matrix.det
              (A.map (indexCompletedArithmeticEval P r level))) =
          PowerSeries.coeff k 1) := by
  let A := orderIndexMatrixFiniteJetLift P r level
    (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level))) n
  refine ⟨A, ?_, ?_, ?_⟩
  · exact orderIndexMatrixFiniteJetLift_to_global_mem_order
      P r level _ n
  · intro i j k hk
    exact orderIndexMatrixFiniteJetLift_coeff P r level _ n i j k hk
  · intro k hk
    exact orderIndexMatrixFiniteJetLift_special_det_coeff
      P r level s n k hk
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
