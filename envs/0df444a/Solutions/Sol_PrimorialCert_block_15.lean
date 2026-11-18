-- Prove2me | solution 1 for PrimorialCert.block_15
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:22.745695+00:00
-- url     : https://prove2.me/submissions/1a9f5c59-2249-490a-bf67-664515a2682b

import Definitions.Def_PrimorialCertData_15

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData15.q0 : PrimData15.s0.bok = true := by decide +kernel
theorem PrimData15.q1 : PrimData15.s1.bok = true := by decide +kernel
theorem PrimData15.q2 : PrimData15.s2.bok = true := by decide +kernel
theorem PrimData15.q3 : PrimData15.s3.bok = true := by decide +kernel
theorem PrimData15.q4 : PrimData15.s4.bok = true := by decide +kernel
theorem PrimData15.q5 : PrimData15.s5.bok = true := by decide +kernel
theorem PrimData15.q6 : PrimData15.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData15.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData15.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData15.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData15.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData15.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
