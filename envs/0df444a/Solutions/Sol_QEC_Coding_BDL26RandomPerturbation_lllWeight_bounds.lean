-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.lllWeight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:21:16.306123+00:00
-- url     : https://prove2.me/submissions/f8f0cb6b-c4a8-4357-8ddf-14272c07f860

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (D : ℕ) :
    0 < lllWeight D ∧ lllWeight D ≤ 1/2 ∧ lllWeight D < 1 := by
  have hd : 0 < 2*((D : ℝ)+1) := by positivity
  have hpos : 0 < lllWeight D := by unfold lllWeight; positivity
  have hhalf : lllWeight D ≤ 1/2 := by
    unfold lllWeight
    apply (div_le_iff₀ hd).mpr
    have hn : (0 : ℝ) ≤ D := by positivity
    nlinarith
  exact ⟨hpos,hhalf,by linarith⟩
end QEC.Coding.BDL26RandomPerturbation
