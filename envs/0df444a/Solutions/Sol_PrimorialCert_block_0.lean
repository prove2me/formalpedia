-- Prove2me | solution 1 for PrimorialCert.block_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:12:44.324616+00:00
-- url     : https://prove2.me/submissions/e742a762-fd52-4d40-9a51-3d51ceaa80ee

import Definitions.Def_PrimorialCertData_0

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData0.q0 : PrimData0.s0.bok = true := by decide +kernel
theorem PrimData0.q1 : PrimData0.s1.bok = true := by decide +kernel
theorem PrimData0.q2 : PrimData0.s2.bok = true := by decide +kernel
theorem PrimData0.q3 : PrimData0.s3.bok = true := by decide +kernel
theorem PrimData0.q4 : PrimData0.s4.bok = true := by decide +kernel
theorem PrimData0.q5 : PrimData0.s5.bok = true := by decide +kernel
theorem PrimData0.q6 : PrimData0.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData0.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData0.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData0.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData0.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData0.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
