-- Prove2me | solution 1 for PrimorialCert.block_17
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:26.852955+00:00
-- url     : https://prove2.me/submissions/f7d3635c-b65a-4e59-8665-9dbabe59ea01

import Definitions.Def_PrimorialCertData_17

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData17.q0 : PrimData17.s0.bok = true := by decide +kernel
theorem PrimData17.q1 : PrimData17.s1.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData17.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData17.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData17.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData17.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData17.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData17.q1, List.forall_mem_nil _⟩⟩,
   by decide +kernel, by decide +kernel⟩
