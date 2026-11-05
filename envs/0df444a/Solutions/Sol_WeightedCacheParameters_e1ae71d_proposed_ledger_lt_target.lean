-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.proposed_ledger_lt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:11:31.375577+00:00
-- url     : https://prove2.me/submissions/b099735b-b572-4fc6-a1c9-21a6d66eee7b

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Hn_pos
import Theorems.Thm_WeightedCacheParameters_e1ae71d_numerator_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
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
end WeightedCacheParameters_e1ae71d
