-- Prove2me | solution 1 for PrimorialCert.block_7
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:06.746836+00:00
-- url     : https://prove2.me/submissions/73351154-4ac3-4d77-a468-b064fe7e3706

import Definitions.Def_PrimorialCertData_7

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData7.q0 : PrimData7.s0.bok = true := by decide +kernel
theorem PrimData7.q1 : PrimData7.s1.bok = true := by decide +kernel
theorem PrimData7.q2 : PrimData7.s2.bok = true := by decide +kernel
theorem PrimData7.q3 : PrimData7.s3.bok = true := by decide +kernel
theorem PrimData7.q4 : PrimData7.s4.bok = true := by decide +kernel
theorem PrimData7.q5 : PrimData7.s5.bok = true := by decide +kernel
theorem PrimData7.q6 : PrimData7.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData7.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData7.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData7.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData7.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData7.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
