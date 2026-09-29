-- Prove2me | solution 1 for R03CycleCandidateV4.bad_creation_cases
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:27:21.727792+00:00
-- url     : https://prove2.me/submissions/cf7e910e-4b63-4795-83f0-c0be61144eeb

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_b1e1659078_v4_CycleTransitions

/- Candidate-only local transition certificates. Codes are 0 unused,
   1 incoming, 2 outgoing; a cycle adds t on its entering half-edge and
   -t = 2*t on its leaving half-edge. Global graph faithfulness is separate.
   Degree-count definitions reuse the frozen v3_ChargePatterns candidate. -/
namespace R03CycleCandidateV4
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem circulation_preserves_charge : ∀ a b c t : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 →
    ((a+t).val + (b+2*t).val + c.val) % 3 = 2 := by
  decide +kernel


end R03CycleCandidateV4

open R03CycleCandidateV4
theorem solution : ∀ a b c t : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 → t ≠ 0 →
    bad a b c = 0 → bad (a+t) (b+2*t) c = 1 →
    ((ins a b c = 2 ∧ outs a b c = 0) ∧
      ((a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0))) ∨
    ((ins a b c = 0 ∧ outs a b c = 1) ∧ a = 0 ∧ b = 0) := by
  decide +kernel
