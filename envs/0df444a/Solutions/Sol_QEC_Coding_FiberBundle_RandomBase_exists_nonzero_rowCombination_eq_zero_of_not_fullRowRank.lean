-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exists_nonzero_rowCombination_eq_zero_of_not_fullRowRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:51:51.265189+00:00
-- url     : https://prove2.me/submissions/09b449c5-f56a-4ccd-90e0-92fde6f93390

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_hasFullRowRank_of_rowCombination_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} {sample : Sample r} (h : ¬HasFullRowRank sample) :
    ∃ coeff : Fin (3 * r) → ZMod 2,
      coeff ≠ 0 ∧ rowCombination sample coeff = 0 := by
  have hnotinj :
      ¬Function.Injective (fun coeff : Fin (3 * r) → ZMod 2 =>
        rowCombination sample coeff) := by
    intro hinj
    exact h (hasFullRowRank_of_rowCombination_injective hinj)
  rw [Function.not_injective_iff] at hnotinj
  rcases hnotinj with ⟨x, y, heq, hxy⟩
  refine ⟨x - y, sub_ne_zero.mpr hxy, ?_⟩
  change Matrix.vecMul (x - y) (boundary sample) = 0
  change (boundary sample).vecMulLinear (x - y) = 0
  rw [map_sub]
  change Matrix.vecMul x (boundary sample) -
    Matrix.vecMul y (boundary sample) = 0
  change rowCombination sample x - rowCombination sample y = 0
  rw [heq, sub_self]
end QEC.Coding.FiberBundle.RandomBase
