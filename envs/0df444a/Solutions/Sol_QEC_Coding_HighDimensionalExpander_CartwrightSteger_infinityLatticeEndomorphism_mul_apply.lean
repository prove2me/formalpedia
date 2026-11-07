-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityLatticeEndomorphism_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:37.324967+00:00
-- url     : https://prove2.me/submissions/18bad5d6-27c1-4990-80b5-0509a3464f1f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (g h : Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (SplittingFunctionField P r))
    (hg : PreservesInfinityCyclicLattice P r g)
    (hh : PreservesInfinityCyclicLattice P r h)
    (X : InfinityCyclicLattice P r) :
    infinityLatticeEndomorphism P r (g * h) (hg.mul P r hh) X =
      infinityLatticeEndomorphism P r g hg
        (infinityLatticeEndomorphism P r h hh X) := by
  apply Subtype.ext
  exact infinityConjugationLinearMap_mul_apply P r g h X.1
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
