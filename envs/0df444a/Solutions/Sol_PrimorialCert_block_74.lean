-- Prove2me | solution 1 for PrimorialCert.block_74
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:19.328891+00:00
-- url     : https://prove2.me/submissions/996e84d0-e2fd-4b3a-89f7-8e76fbf364df

import Definitions.Def_PrimorialCertData_74

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData74.q0 : PrimData74.s0.bok = true := by decide +kernel
theorem PrimData74.q1 : PrimData74.s1.bok = true := by decide +kernel
theorem PrimData74.q2 : PrimData74.s2.bok = true := by decide +kernel
theorem PrimData74.q3 : PrimData74.s3.bok = true := by decide +kernel
theorem PrimData74.q4 : PrimData74.s4.bok = true := by decide +kernel
theorem PrimData74.q5 : PrimData74.s5.bok = true := by decide +kernel
theorem PrimData74.q6 : PrimData74.s6.bok = true := by decide +kernel
theorem PrimData74.q7 : PrimData74.s7.bok = true := by decide +kernel
theorem PrimData74.q8 : PrimData74.s8.bok = true := by decide +kernel
theorem PrimData74.q9 : PrimData74.s9.bok = true := by decide +kernel
theorem PrimData74.q10 : PrimData74.s10.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData74.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData74.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData74.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData74.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData74.q10, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
