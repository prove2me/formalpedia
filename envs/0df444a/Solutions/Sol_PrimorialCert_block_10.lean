-- Prove2me | solution 1 for PrimorialCert.block_10
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:12.89946+00:00
-- url     : https://prove2.me/submissions/b12fd8a1-c270-42ff-a18c-1769ef1fa6c9

import Definitions.Def_PrimorialCertData_10

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData10.q0 : PrimData10.s0.bok = true := by decide +kernel
theorem PrimData10.q1 : PrimData10.s1.bok = true := by decide +kernel
theorem PrimData10.q2 : PrimData10.s2.bok = true := by decide +kernel
theorem PrimData10.q3 : PrimData10.s3.bok = true := by decide +kernel
theorem PrimData10.q4 : PrimData10.s4.bok = true := by decide +kernel
theorem PrimData10.q5 : PrimData10.s5.bok = true := by decide +kernel
theorem PrimData10.q6 : PrimData10.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData10.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData10.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData10.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData10.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData10.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
