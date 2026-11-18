-- Prove2me | solution 1 for PrimorialCert.block_35
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:02.933207+00:00
-- url     : https://prove2.me/submissions/6f3018a8-3fcb-481b-88f6-a7bad2c1361b

import Definitions.Def_PrimorialCertData_35

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData35.q0 : PrimData35.s0.bok = true := by decide +kernel
theorem PrimData35.q1 : PrimData35.s1.bok = true := by decide +kernel
theorem PrimData35.q2 : PrimData35.s2.bok = true := by decide +kernel
theorem PrimData35.q3 : PrimData35.s3.bok = true := by decide +kernel
theorem PrimData35.q4 : PrimData35.s4.bok = true := by decide +kernel
theorem PrimData35.q5 : PrimData35.s5.bok = true := by decide +kernel
theorem PrimData35.q6 : PrimData35.s6.bok = true := by decide +kernel
theorem PrimData35.q7 : PrimData35.s7.bok = true := by decide +kernel
theorem PrimData35.q8 : PrimData35.s8.bok = true := by decide +kernel
theorem PrimData35.q9 : PrimData35.s9.bok = true := by decide +kernel
theorem PrimData35.q10 : PrimData35.s10.bok = true := by decide +kernel
theorem PrimData35.q11 : PrimData35.s11.bok = true := by decide +kernel
theorem PrimData35.q12 : PrimData35.s12.bok = true := by decide +kernel
theorem PrimData35.q13 : PrimData35.s13.bok = true := by decide +kernel
theorem PrimData35.q14 : PrimData35.s14.bok = true := by decide +kernel
theorem PrimData35.q15 : PrimData35.s15.bok = true := by decide +kernel
theorem PrimData35.q16 : PrimData35.s16.bok = true := by decide +kernel
theorem PrimData35.q17 : PrimData35.s17.bok = true := by decide +kernel
theorem PrimData35.q18 : PrimData35.s18.bok = true := by decide +kernel
theorem PrimData35.q19 : PrimData35.s19.bok = true := by decide +kernel
theorem PrimData35.q20 : PrimData35.s20.bok = true := by decide +kernel
theorem PrimData35.q21 : PrimData35.s21.bok = true := by decide +kernel
theorem PrimData35.q22 : PrimData35.s22.bok = true := by decide +kernel
theorem PrimData35.q23 : PrimData35.s23.bok = true := by decide +kernel
theorem PrimData35.q24 : PrimData35.s24.bok = true := by decide +kernel
theorem PrimData35.q25 : PrimData35.s25.bok = true := by decide +kernel
theorem PrimData35.q26 : PrimData35.s26.bok = true := by decide +kernel
theorem PrimData35.q27 : PrimData35.s27.bok = true := by decide +kernel
theorem PrimData35.q28 : PrimData35.s28.bok = true := by decide +kernel
theorem PrimData35.q29 : PrimData35.s29.bok = true := by decide +kernel
theorem PrimData35.q30 : PrimData35.s30.bok = true := by decide +kernel
theorem PrimData35.q31 : PrimData35.s31.bok = true := by decide +kernel
theorem PrimData35.q32 : PrimData35.s32.bok = true := by decide +kernel
theorem PrimData35.q33 : PrimData35.s33.bok = true := by decide +kernel
theorem PrimData35.q34 : PrimData35.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData35.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData35.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData35.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData35.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData35.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
