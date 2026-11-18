-- Prove2me | solution 1 for PrimorialCert.block_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:27:56.723938+00:00
-- url     : https://prove2.me/submissions/db3fe128-91c0-4ca9-bee8-b9c6e975151a

import Definitions.Def_PrimorialCertData_2

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData2.q0 : PrimData2.s0.bok = true := by decide +kernel
theorem PrimData2.q1 : PrimData2.s1.bok = true := by decide +kernel
theorem PrimData2.q2 : PrimData2.s2.bok = true := by decide +kernel
theorem PrimData2.q3 : PrimData2.s3.bok = true := by decide +kernel
theorem PrimData2.q4 : PrimData2.s4.bok = true := by decide +kernel
theorem PrimData2.q5 : PrimData2.s5.bok = true := by decide +kernel
theorem PrimData2.q6 : PrimData2.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData2.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData2.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData2.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData2.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData2.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
