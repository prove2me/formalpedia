-- Prove2me | solution 1 for PrimorialCert.block_54
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:39.089877+00:00
-- url     : https://prove2.me/submissions/e4b6015c-a68d-4f8e-9106-c9da90d5607f

import Definitions.Def_PrimorialCertData_54

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData54.q0 : PrimData54.s0.bok = true := by decide +kernel
theorem PrimData54.q1 : PrimData54.s1.bok = true := by decide +kernel
theorem PrimData54.q2 : PrimData54.s2.bok = true := by decide +kernel
theorem PrimData54.q3 : PrimData54.s3.bok = true := by decide +kernel
theorem PrimData54.q4 : PrimData54.s4.bok = true := by decide +kernel
theorem PrimData54.q5 : PrimData54.s5.bok = true := by decide +kernel
theorem PrimData54.q6 : PrimData54.s6.bok = true := by decide +kernel
theorem PrimData54.q7 : PrimData54.s7.bok = true := by decide +kernel
theorem PrimData54.q8 : PrimData54.s8.bok = true := by decide +kernel
theorem PrimData54.q9 : PrimData54.s9.bok = true := by decide +kernel
theorem PrimData54.q10 : PrimData54.s10.bok = true := by decide +kernel
theorem PrimData54.q11 : PrimData54.s11.bok = true := by decide +kernel
theorem PrimData54.q12 : PrimData54.s12.bok = true := by decide +kernel
theorem PrimData54.q13 : PrimData54.s13.bok = true := by decide +kernel
theorem PrimData54.q14 : PrimData54.s14.bok = true := by decide +kernel
theorem PrimData54.q15 : PrimData54.s15.bok = true := by decide +kernel
theorem PrimData54.q16 : PrimData54.s16.bok = true := by decide +kernel
theorem PrimData54.q17 : PrimData54.s17.bok = true := by decide +kernel
theorem PrimData54.q18 : PrimData54.s18.bok = true := by decide +kernel
theorem PrimData54.q19 : PrimData54.s19.bok = true := by decide +kernel
theorem PrimData54.q20 : PrimData54.s20.bok = true := by decide +kernel
theorem PrimData54.q21 : PrimData54.s21.bok = true := by decide +kernel
theorem PrimData54.q22 : PrimData54.s22.bok = true := by decide +kernel
theorem PrimData54.q23 : PrimData54.s23.bok = true := by decide +kernel
theorem PrimData54.q24 : PrimData54.s24.bok = true := by decide +kernel
theorem PrimData54.q25 : PrimData54.s25.bok = true := by decide +kernel
theorem PrimData54.q26 : PrimData54.s26.bok = true := by decide +kernel
theorem PrimData54.q27 : PrimData54.s27.bok = true := by decide +kernel
theorem PrimData54.q28 : PrimData54.s28.bok = true := by decide +kernel
theorem PrimData54.q29 : PrimData54.s29.bok = true := by decide +kernel
theorem PrimData54.q30 : PrimData54.s30.bok = true := by decide +kernel
theorem PrimData54.q31 : PrimData54.s31.bok = true := by decide +kernel
theorem PrimData54.q32 : PrimData54.s32.bok = true := by decide +kernel
theorem PrimData54.q33 : PrimData54.s33.bok = true := by decide +kernel
theorem PrimData54.q34 : PrimData54.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData54.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData54.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData54.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData54.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData54.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
