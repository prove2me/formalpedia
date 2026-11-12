-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexFiniteJetNormOneCompletedInnerFormLift_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:44:58.361357+00:00
-- url     : https://prove2.me/submissions/6ac70cab-2b0d-4243-9ea2-df561b67b90d

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexFiniteJetNormOneCompletedLift_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : IndexCompletedNormOneInnerForm P r level)
    (n : Nat) (hn : 0 < n)
    (i j : Fin r.matrixRank) (k : Nat) (hk : k < n) :
    PowerSeries.coeff k
        (((orderIndexFiniteJetNormOneCompletedInnerFormLift
            P r level s n hn :
          Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) =
      PowerSeries.coeff k
        (((s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (PowerSeries (ResidueField P r level))) i j) :=
  orderIndexFiniteJetNormOneCompletedLift_coeff
    P r level s n hn i j k hk
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
