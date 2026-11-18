-- Prove2me | solution 1 for PrimorialCert.block_16
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:24.757259+00:00
-- url     : https://prove2.me/submissions/03fc2065-57c4-4c23-83d6-307f0867037c

import Definitions.Def_PrimorialCertData_16

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData16.q0 : PrimData16.s0.bok = true := by decide +kernel
theorem PrimData16.q1 : PrimData16.s1.bok = true := by decide +kernel
theorem PrimData16.q2 : PrimData16.s2.bok = true := by decide +kernel
theorem PrimData16.q3 : PrimData16.s3.bok = true := by decide +kernel
theorem PrimData16.q4 : PrimData16.s4.bok = true := by decide +kernel
theorem PrimData16.q5 : PrimData16.s5.bok = true := by decide +kernel
theorem PrimData16.q6 : PrimData16.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData16.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData16.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData16.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData16.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData16.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
