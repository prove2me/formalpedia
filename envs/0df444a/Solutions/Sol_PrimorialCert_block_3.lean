-- Prove2me | solution 1 for PrimorialCert.block_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:27:58.715579+00:00
-- url     : https://prove2.me/submissions/5aefb448-4793-472b-a299-fc9f0e5d5f2a

import Definitions.Def_PrimorialCertData_3

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData3.q0 : PrimData3.s0.bok = true := by decide +kernel
theorem PrimData3.q1 : PrimData3.s1.bok = true := by decide +kernel
theorem PrimData3.q2 : PrimData3.s2.bok = true := by decide +kernel
theorem PrimData3.q3 : PrimData3.s3.bok = true := by decide +kernel
theorem PrimData3.q4 : PrimData3.s4.bok = true := by decide +kernel
theorem PrimData3.q5 : PrimData3.s5.bok = true := by decide +kernel
theorem PrimData3.q6 : PrimData3.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData3.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData3.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData3.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData3.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData3.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
