-- Prove2me | solution 1 for PrimorialCert.block_52
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:35.104316+00:00
-- url     : https://prove2.me/submissions/aeee68d2-e30a-41cb-b67a-ee13808f095f

import Definitions.Def_PrimorialCertData_52

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData52.q0 : PrimData52.s0.bok = true := by decide +kernel
theorem PrimData52.q1 : PrimData52.s1.bok = true := by decide +kernel
theorem PrimData52.q2 : PrimData52.s2.bok = true := by decide +kernel
theorem PrimData52.q3 : PrimData52.s3.bok = true := by decide +kernel
theorem PrimData52.q4 : PrimData52.s4.bok = true := by decide +kernel
theorem PrimData52.q5 : PrimData52.s5.bok = true := by decide +kernel
theorem PrimData52.q6 : PrimData52.s6.bok = true := by decide +kernel
theorem PrimData52.q7 : PrimData52.s7.bok = true := by decide +kernel
theorem PrimData52.q8 : PrimData52.s8.bok = true := by decide +kernel
theorem PrimData52.q9 : PrimData52.s9.bok = true := by decide +kernel
theorem PrimData52.q10 : PrimData52.s10.bok = true := by decide +kernel
theorem PrimData52.q11 : PrimData52.s11.bok = true := by decide +kernel
theorem PrimData52.q12 : PrimData52.s12.bok = true := by decide +kernel
theorem PrimData52.q13 : PrimData52.s13.bok = true := by decide +kernel
theorem PrimData52.q14 : PrimData52.s14.bok = true := by decide +kernel
theorem PrimData52.q15 : PrimData52.s15.bok = true := by decide +kernel
theorem PrimData52.q16 : PrimData52.s16.bok = true := by decide +kernel
theorem PrimData52.q17 : PrimData52.s17.bok = true := by decide +kernel
theorem PrimData52.q18 : PrimData52.s18.bok = true := by decide +kernel
theorem PrimData52.q19 : PrimData52.s19.bok = true := by decide +kernel
theorem PrimData52.q20 : PrimData52.s20.bok = true := by decide +kernel
theorem PrimData52.q21 : PrimData52.s21.bok = true := by decide +kernel
theorem PrimData52.q22 : PrimData52.s22.bok = true := by decide +kernel
theorem PrimData52.q23 : PrimData52.s23.bok = true := by decide +kernel
theorem PrimData52.q24 : PrimData52.s24.bok = true := by decide +kernel
theorem PrimData52.q25 : PrimData52.s25.bok = true := by decide +kernel
theorem PrimData52.q26 : PrimData52.s26.bok = true := by decide +kernel
theorem PrimData52.q27 : PrimData52.s27.bok = true := by decide +kernel
theorem PrimData52.q28 : PrimData52.s28.bok = true := by decide +kernel
theorem PrimData52.q29 : PrimData52.s29.bok = true := by decide +kernel
theorem PrimData52.q30 : PrimData52.s30.bok = true := by decide +kernel
theorem PrimData52.q31 : PrimData52.s31.bok = true := by decide +kernel
theorem PrimData52.q32 : PrimData52.s32.bok = true := by decide +kernel
theorem PrimData52.q33 : PrimData52.s33.bok = true := by decide +kernel
theorem PrimData52.q34 : PrimData52.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData52.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData52.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData52.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData52.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData52.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
