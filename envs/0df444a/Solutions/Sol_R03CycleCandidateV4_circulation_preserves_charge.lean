-- Prove2me | solution 1 for R03CycleCandidateV4.circulation_preserves_charge
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:23.038126+00:00
-- url     : https://prove2.me/submissions/3db5a625-ecd1-419b-a87b-a956636a846c

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_b1e1659078_v4_CycleTransitions

/- Candidate-only local transition certificates. Codes are 0 unused,
   1 incoming, 2 outgoing; a cycle adds t on its entering half-edge and
   -t = 2*t on its leaving half-edge. Global graph faithfulness is separate.
   Degree-count definitions reuse the frozen v3_ChargePatterns candidate. -/
namespace R03CycleCandidateV4
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

end R03CycleCandidateV4

open R03CycleCandidateV4
theorem solution : ∀ a b c t : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 →
    ((a+t).val + (b+2*t).val + c.val) % 3 = 2 := by
  decide +kernel
