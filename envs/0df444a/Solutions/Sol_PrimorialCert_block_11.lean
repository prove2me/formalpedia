-- Prove2me | solution 1 for PrimorialCert.block_11
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:14.80776+00:00
-- url     : https://prove2.me/submissions/98bce9bc-12c6-4190-ae4c-1374a1419589

import Definitions.Def_PrimorialCertData_11

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData11.q0 : PrimData11.s0.bok = true := by decide +kernel
theorem PrimData11.q1 : PrimData11.s1.bok = true := by decide +kernel
theorem PrimData11.q2 : PrimData11.s2.bok = true := by decide +kernel
theorem PrimData11.q3 : PrimData11.s3.bok = true := by decide +kernel
theorem PrimData11.q4 : PrimData11.s4.bok = true := by decide +kernel
theorem PrimData11.q5 : PrimData11.s5.bok = true := by decide +kernel
theorem PrimData11.q6 : PrimData11.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData11.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData11.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData11.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData11.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData11.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
