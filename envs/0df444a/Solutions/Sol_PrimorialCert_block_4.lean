-- Prove2me | solution 1 for PrimorialCert.block_4
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:00.67128+00:00
-- url     : https://prove2.me/submissions/febd6242-bf21-4b12-900a-9816a05566ba

import Definitions.Def_PrimorialCertData_4

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData4.q0 : PrimData4.s0.bok = true := by decide +kernel
theorem PrimData4.q1 : PrimData4.s1.bok = true := by decide +kernel
theorem PrimData4.q2 : PrimData4.s2.bok = true := by decide +kernel
theorem PrimData4.q3 : PrimData4.s3.bok = true := by decide +kernel
theorem PrimData4.q4 : PrimData4.s4.bok = true := by decide +kernel
theorem PrimData4.q5 : PrimData4.s5.bok = true := by decide +kernel
theorem PrimData4.q6 : PrimData4.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData4.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData4.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData4.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData4.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData4.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
