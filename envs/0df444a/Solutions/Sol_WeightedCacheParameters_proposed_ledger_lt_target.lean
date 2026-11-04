-- Prove2me | solution 1 for WeightedCacheParameters.proposed_ledger_lt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:14.197948+00:00
-- url     : https://prove2.me/submissions/03a31937-8db2-4aaa-8e9e-40b29a0c22b4

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_Hn_pos
import Theorems.Thm_WeightedCacheParameters_numerator_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : ∀ t ∈ proposedLedger, t < targetExponent := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := numerator_bounds
  intro t ht
  simp only [proposedLedger, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (div_lt_iff₀ Hn_pos).2 h1
  · exact (div_lt_iff₀ Hn_pos).2 h2
  · exact (div_lt_iff₀ Hn_pos).2 h3
  · exact (div_lt_iff₀ Hn_pos).2 h4
  · exact (div_lt_iff₀ Hn_pos).2 h5
  · norm_num [targetExponent]
end WeightedCacheParameters
