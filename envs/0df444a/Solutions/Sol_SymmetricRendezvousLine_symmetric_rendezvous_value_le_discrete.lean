-- Prove2me | solution 1 for SymmetricRendezvousLine.symmetric_rendezvous_value_le_discrete
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-31T19:10:01.717989+00:00
-- url     : https://prove2.me/submissions/4f818085-2cfb-4514-8c6b-d69aada5879e

import Definitions.Def_SymmetricRendezvousLine_defs

open SymmetricRendezvousLine

/-- The symmetric value is an infimum over *all* mixed strategies, while the discrete value is
the infimum of the same quantity over the subfamily of strategies supported on integer
zigzags; an infimum over a larger family is smaller. -/
theorem solution : symmetricRendezvousValue ≤ discreteSymmetricRendezvousValue :=
  le_iInf₂ fun S _ => iInf_le (fun S : MixedStrategy => expectedMeetingTime S S) S
