-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.abs_norm_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:33.09204+00:00
-- url     : https://prove2.me/submissions/17a4b47a-3091-4803-920e-615f9cd8db6a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] (z : K) :
    |((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by
  rw [neg_eq_neg_one_mul, map_mul, Rat.cast_mul, abs_mul]
  have h1 : (-1 : K) = algebraMap ℚ K (-1) := by simp
  rw [h1, Algebra.norm_algebraMap]
  simp
end ReciprocityTheory.MultiplicativeHeights.SemiPt
