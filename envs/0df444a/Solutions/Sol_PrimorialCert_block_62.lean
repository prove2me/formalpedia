-- Prove2me | solution 1 for PrimorialCert.block_62
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:55.131199+00:00
-- url     : https://prove2.me/submissions/c350b935-78f6-467b-bccf-f34f48809d04

import Definitions.Def_PrimorialCertData_62

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData62.q0 : PrimData62.s0.bok = true := by decide +kernel
theorem PrimData62.q1 : PrimData62.s1.bok = true := by decide +kernel
theorem PrimData62.q2 : PrimData62.s2.bok = true := by decide +kernel
theorem PrimData62.q3 : PrimData62.s3.bok = true := by decide +kernel
theorem PrimData62.q4 : PrimData62.s4.bok = true := by decide +kernel
theorem PrimData62.q5 : PrimData62.s5.bok = true := by decide +kernel
theorem PrimData62.q6 : PrimData62.s6.bok = true := by decide +kernel
theorem PrimData62.q7 : PrimData62.s7.bok = true := by decide +kernel
theorem PrimData62.q8 : PrimData62.s8.bok = true := by decide +kernel
theorem PrimData62.q9 : PrimData62.s9.bok = true := by decide +kernel
theorem PrimData62.q10 : PrimData62.s10.bok = true := by decide +kernel
theorem PrimData62.q11 : PrimData62.s11.bok = true := by decide +kernel
theorem PrimData62.q12 : PrimData62.s12.bok = true := by decide +kernel
theorem PrimData62.q13 : PrimData62.s13.bok = true := by decide +kernel
theorem PrimData62.q14 : PrimData62.s14.bok = true := by decide +kernel
theorem PrimData62.q15 : PrimData62.s15.bok = true := by decide +kernel
theorem PrimData62.q16 : PrimData62.s16.bok = true := by decide +kernel
theorem PrimData62.q17 : PrimData62.s17.bok = true := by decide +kernel
theorem PrimData62.q18 : PrimData62.s18.bok = true := by decide +kernel
theorem PrimData62.q19 : PrimData62.s19.bok = true := by decide +kernel
theorem PrimData62.q20 : PrimData62.s20.bok = true := by decide +kernel
theorem PrimData62.q21 : PrimData62.s21.bok = true := by decide +kernel
theorem PrimData62.q22 : PrimData62.s22.bok = true := by decide +kernel
theorem PrimData62.q23 : PrimData62.s23.bok = true := by decide +kernel
theorem PrimData62.q24 : PrimData62.s24.bok = true := by decide +kernel
theorem PrimData62.q25 : PrimData62.s25.bok = true := by decide +kernel
theorem PrimData62.q26 : PrimData62.s26.bok = true := by decide +kernel
theorem PrimData62.q27 : PrimData62.s27.bok = true := by decide +kernel
theorem PrimData62.q28 : PrimData62.s28.bok = true := by decide +kernel
theorem PrimData62.q29 : PrimData62.s29.bok = true := by decide +kernel
theorem PrimData62.q30 : PrimData62.s30.bok = true := by decide +kernel
theorem PrimData62.q31 : PrimData62.s31.bok = true := by decide +kernel
theorem PrimData62.q32 : PrimData62.s32.bok = true := by decide +kernel
theorem PrimData62.q33 : PrimData62.s33.bok = true := by decide +kernel
theorem PrimData62.q34 : PrimData62.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData62.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData62.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData62.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData62.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData62.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
