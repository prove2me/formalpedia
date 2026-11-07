-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exists_nonempty_subsetRowCombination_eq_zero_of_not_fullRowRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:03:04.910052+00:00
-- url     : https://prove2.me/submissions/36e8fb24-d75d-4f53-b09e-1b908d02000f

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowSupport_nonempty_iff
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_rowCombination_eq_subsetRowCombination
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_nonzero_rowCombination_eq_zero_of_not_fullRowRank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    {r : Nat} {sample : Sample r} (h : ¬HasFullRowRank sample) :
    ∃ A : Finset (Fin (3 * r)),
      A.Nonempty ∧ subsetRowCombination sample A = 0 := by
  rcases exists_nonzero_rowCombination_eq_zero_of_not_fullRowRank h with
    ⟨coeff, hcoeff, hzero⟩
  refine ⟨rowSupport coeff, (rowSupport_nonempty_iff coeff).2 hcoeff, ?_⟩
  rw [← rowCombination_eq_subsetRowCombination sample coeff]
  exact hzero
end QEC.Coding.FiberBundle.RandomBase
