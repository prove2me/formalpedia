-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetNormOneCompletedLift_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:15:11.098366+00:00
-- url     : https://prove2.me/submissions/b49373c0-4e5d-419a-971c-c0d3d4d1332f

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_powerSeries_inv_finite_coeff_eq_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexFiniteJetDetRoot_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) (hn : 0 < n)
    (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (orderIndexFiniteJetNormOneCompletedLift P r level s n hn i j) =
      PowerSeries.coeff k
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) := by
  rw [orderIndexFiniteJetNormOneCompletedLift, Matrix.smul_apply,
    smul_eq_mul]
  calc
    _ = PowerSeries.coeff k
        (1 * (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j)) := by
      apply powerSeries_coeff_mul_eq_of_finite_coeff_eq
      · exact powerSeries_inv_finite_coeff_eq_one
          (orderIndexFiniteJetDetRoot P r level s n hn) n
          (orderIndexFiniteJetDetRoot_constantCoeff P r level s n hn)
          (fun m hm => orderIndexFiniteJetDetRoot_coeff
            P r level s n hn m hm)
      · intro m hm
        exact orderIndexMatrixFiniteJetLift_coeff P r level _ n i j m hm
      · exact hk
    _ = _ := by rw [one_mul]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
