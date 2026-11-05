-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.numerator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:39.267376+00:00
-- url     : https://prove2.me/submissions/42619d4a-0102-465e-ba6c-c7e73f6e8b76

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Hn_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_An_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Gn_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Bn_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Qn_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
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
end WeightedCacheParameters_e1ae71d
