-- Prove2me | solution 1 for PrimorialCert.block_6
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:04.720027+00:00
-- url     : https://prove2.me/submissions/b1a1605e-c0af-4c9f-aceb-f4664109a48a

import Definitions.Def_PrimorialCertData_6

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData6.q0 : PrimData6.s0.bok = true := by decide +kernel
theorem PrimData6.q1 : PrimData6.s1.bok = true := by decide +kernel
theorem PrimData6.q2 : PrimData6.s2.bok = true := by decide +kernel
theorem PrimData6.q3 : PrimData6.s3.bok = true := by decide +kernel
theorem PrimData6.q4 : PrimData6.s4.bok = true := by decide +kernel
theorem PrimData6.q5 : PrimData6.s5.bok = true := by decide +kernel
theorem PrimData6.q6 : PrimData6.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData6.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData6.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData6.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData6.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData6.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
