-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.theorem_9_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:16:51.025355+00:00
-- url     : https://prove2.me/submissions/177b1f46-9b8f-410f-b849-11c1a7e79f5b

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Model
import Definitions.Def_TwoAgentSched_TotalTotal_Construction
import Theorems.Thm_TwoAgentSched_TotalTotal_totalTotal_encoding_reduction
import Theorems.Thm_TwoAgentSched_TotalTotal_theorem_9_2_equivalence

open TwoAgentSched.TotalTotal CookPvsNP ProjSchedTW.Complexity

theorem solution : PolyReducible partitionLang targetLang := by
  rcases totalTotal_encoding_reduction with ⟨f, hf_poly, hf_spec⟩
  refine ⟨f, hf_poly, fun x => ?_⟩
  rcases hf_spec x with ⟨k, p, hp, hpart, hrec⟩
  have hQ : thresholdQ p = (bigT p : ℝ) / 2 := by
    unfold thresholdQ bigT
    push_cast
    ring
  rw [hpart, theorem_9_2_equivalence p hp, ← hQ, hrec]
