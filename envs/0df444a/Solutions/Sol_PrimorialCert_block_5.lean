-- Prove2me | solution 1 for PrimorialCert.block_5
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:02.659037+00:00
-- url     : https://prove2.me/submissions/f22244b8-8cb0-4ac0-8678-8e451ee4e3b1

import Definitions.Def_PrimorialCertData_5

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData5.q0 : PrimData5.s0.bok = true := by decide +kernel
theorem PrimData5.q1 : PrimData5.s1.bok = true := by decide +kernel
theorem PrimData5.q2 : PrimData5.s2.bok = true := by decide +kernel
theorem PrimData5.q3 : PrimData5.s3.bok = true := by decide +kernel
theorem PrimData5.q4 : PrimData5.s4.bok = true := by decide +kernel
theorem PrimData5.q5 : PrimData5.s5.bok = true := by decide +kernel
theorem PrimData5.q6 : PrimData5.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData5.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData5.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData5.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData5.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData5.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
