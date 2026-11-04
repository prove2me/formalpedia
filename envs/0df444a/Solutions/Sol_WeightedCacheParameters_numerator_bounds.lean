-- Prove2me | solution 1 for WeightedCacheParameters.numerator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:26.150199+00:00
-- url     : https://prove2.me/submissions/5ca57d37-cdf0-45ba-8310-4341a68a7ad2

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_Hn_bounds
import Theorems.Thm_WeightedCacheParameters_An_bounds
import Theorems.Thm_WeightedCacheParameters_Gn_bounds
import Theorems.Thm_WeightedCacheParameters_Bn_bounds
import Theorems.Thm_WeightedCacheParameters_Qn_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution :
    2 * Bn < targetExponent * Hn ∧
    2 * Hn - Gn + 2 * Qn < targetExponent * Hn ∧
    2 * An < targetExponent * Hn ∧
    Hn + Gn < targetExponent * Hn ∧
    2 * Hn - Gn < targetExponent * Hn := by
  obtain ⟨hH0, hH1⟩ := Hn_bounds
  obtain ⟨hA0, hA1⟩ := An_bounds
  obtain ⟨hG0, hG1⟩ := Gn_bounds
  obtain ⟨hB0, hB1⟩ := Bn_bounds
  obtain ⟨hQ0, hQ1⟩ := Qn_bounds
  norm_num [targetExponent] at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
end WeightedCacheParameters
