-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.rpp_tree_matching_runtime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T14:43:48.954019+00:00
-- url     : https://prove2.me/submissions/c37e3f94-86e9-4109-b757-9282506c095f

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part07
import Theorems.Thm_VehicleRoutingSurvey_Routing_compact_matching_cubic_exists

open VehicleRoutingSurvey.Routing in
theorem solution :
    ∃ (p : List ArithmeticInstruction) (C N : ℕ), RuralImplementation p C N := by
  obtain ⟨block, checked⟩ := compact_matching_cubic_exists
  exact ⟨ruralRAMProgram block, 56365, 0, ruralRAMProgram_correct checked⟩
