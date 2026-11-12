-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetDetRoot_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:13:12.181195+00:00
-- url     : https://prove2.me/submissions/95173e0e-357f-4e66-ba4b-0ec9c599c081

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_powerSeries_root_finite_coeff_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (orderIndexFiniteJetDetRoot P r level s n hn) =
      PowerSeries.coeff k 1 := by
  apply powerSeries_root_finite_coeff_eq_one P r level
      (orderIndexFiniteJetDetRoot P r level s n hn)
      (Matrix.det
        ((orderIndexMatrixFiniteJetLift P r level
            (s : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
              (PowerSeries (ResidueField P r level))) n).map
          (indexCompletedArithmeticEval P r level))) n
  · exact orderIndexFiniteJetDetRoot_pow P r level s n hn
  · exact orderIndexFiniteJetDetRoot_constantCoeff P r level s n hn
  · intro m hm
    exact orderIndexMatrixFiniteJetLift_special_det_coeff
      P r level s n m hm
  · exact hk
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
