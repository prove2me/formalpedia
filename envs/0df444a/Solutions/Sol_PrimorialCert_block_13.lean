-- Prove2me | solution 1 for PrimorialCert.block_13
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:18.69945+00:00
-- url     : https://prove2.me/submissions/5ab856d7-1e28-425d-a470-3bde29aba56e

import Definitions.Def_PrimorialCertData_13

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData13.q0 : PrimData13.s0.bok = true := by decide +kernel
theorem PrimData13.q1 : PrimData13.s1.bok = true := by decide +kernel
theorem PrimData13.q2 : PrimData13.s2.bok = true := by decide +kernel
theorem PrimData13.q3 : PrimData13.s3.bok = true := by decide +kernel
theorem PrimData13.q4 : PrimData13.s4.bok = true := by decide +kernel
theorem PrimData13.q5 : PrimData13.s5.bok = true := by decide +kernel
theorem PrimData13.q6 : PrimData13.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData13.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData13.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData13.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData13.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData13.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
