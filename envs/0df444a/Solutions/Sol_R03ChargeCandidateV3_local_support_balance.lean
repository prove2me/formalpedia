-- Prove2me | solution 1 for R03ChargeCandidateV3.local_support_balance
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T19:51:54.386497+00:00
-- url     : https://prove2.me/submissions/e27a4650-053b-4cac-b4bd-e05ec2488ee0

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_r03_defs_04051951db_v3_ChargePatterns

/- Local arithmetic candidates for a cubic vertex, not a graph-level proof.
   Fin 3 codes: 0 unused, 1 incoming, 2 outgoing. -/
namespace R03ChargeCandidateV3
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem charge_two_patterns : ∀ a b c : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 ↔
      (ins a b c = 2 ∧ outs a b c = 0) ∨
      (ins a b c = 0 ∧ outs a b c = 1) ∨
      (ins a b c = 1 ∧ outs a b c = 2) := by
  decide +kernel

theorem local_center_balance : ∀ a b c : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 →
      ins a b c + 1 = outs a b c + 3 * isCenter a b c := by
  decide +kernel


end R03ChargeCandidateV3

open R03ChargeCandidateV3
theorem solution : ∀ a b c : Fin 3,
    (a.val + b.val + c.val) % 3 = 2 →
      ins a b c + outs a b c = 1 + isCenter a b c + 2 * isBad a b c := by
  decide +kernel
