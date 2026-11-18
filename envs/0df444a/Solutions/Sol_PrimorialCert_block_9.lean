-- Prove2me | solution 1 for PrimorialCert.block_9
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:10.71636+00:00
-- url     : https://prove2.me/submissions/4e55ddf9-32db-4af9-9719-fda97e52729b

import Definitions.Def_PrimorialCertData_9

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData9.q0 : PrimData9.s0.bok = true := by decide +kernel
theorem PrimData9.q1 : PrimData9.s1.bok = true := by decide +kernel
theorem PrimData9.q2 : PrimData9.s2.bok = true := by decide +kernel
theorem PrimData9.q3 : PrimData9.s3.bok = true := by decide +kernel
theorem PrimData9.q4 : PrimData9.s4.bok = true := by decide +kernel
theorem PrimData9.q5 : PrimData9.s5.bok = true := by decide +kernel
theorem PrimData9.q6 : PrimData9.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData9.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData9.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData9.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData9.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData9.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
