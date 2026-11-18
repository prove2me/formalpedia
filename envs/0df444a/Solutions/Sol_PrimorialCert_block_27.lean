-- Prove2me | solution 1 for PrimorialCert.block_27
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:46.812296+00:00
-- url     : https://prove2.me/submissions/e85051d2-932e-4122-b208-d11bf606db7c

import Definitions.Def_PrimorialCertData_27

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData27.q0 : PrimData27.s0.bok = true := by decide +kernel
theorem PrimData27.q1 : PrimData27.s1.bok = true := by decide +kernel
theorem PrimData27.q2 : PrimData27.s2.bok = true := by decide +kernel
theorem PrimData27.q3 : PrimData27.s3.bok = true := by decide +kernel
theorem PrimData27.q4 : PrimData27.s4.bok = true := by decide +kernel
theorem PrimData27.q5 : PrimData27.s5.bok = true := by decide +kernel
theorem PrimData27.q6 : PrimData27.s6.bok = true := by decide +kernel
theorem PrimData27.q7 : PrimData27.s7.bok = true := by decide +kernel
theorem PrimData27.q8 : PrimData27.s8.bok = true := by decide +kernel
theorem PrimData27.q9 : PrimData27.s9.bok = true := by decide +kernel
theorem PrimData27.q10 : PrimData27.s10.bok = true := by decide +kernel
theorem PrimData27.q11 : PrimData27.s11.bok = true := by decide +kernel
theorem PrimData27.q12 : PrimData27.s12.bok = true := by decide +kernel
theorem PrimData27.q13 : PrimData27.s13.bok = true := by decide +kernel
theorem PrimData27.q14 : PrimData27.s14.bok = true := by decide +kernel
theorem PrimData27.q15 : PrimData27.s15.bok = true := by decide +kernel
theorem PrimData27.q16 : PrimData27.s16.bok = true := by decide +kernel
theorem PrimData27.q17 : PrimData27.s17.bok = true := by decide +kernel
theorem PrimData27.q18 : PrimData27.s18.bok = true := by decide +kernel
theorem PrimData27.q19 : PrimData27.s19.bok = true := by decide +kernel
theorem PrimData27.q20 : PrimData27.s20.bok = true := by decide +kernel
theorem PrimData27.q21 : PrimData27.s21.bok = true := by decide +kernel
theorem PrimData27.q22 : PrimData27.s22.bok = true := by decide +kernel
theorem PrimData27.q23 : PrimData27.s23.bok = true := by decide +kernel
theorem PrimData27.q24 : PrimData27.s24.bok = true := by decide +kernel
theorem PrimData27.q25 : PrimData27.s25.bok = true := by decide +kernel
theorem PrimData27.q26 : PrimData27.s26.bok = true := by decide +kernel
theorem PrimData27.q27 : PrimData27.s27.bok = true := by decide +kernel
theorem PrimData27.q28 : PrimData27.s28.bok = true := by decide +kernel
theorem PrimData27.q29 : PrimData27.s29.bok = true := by decide +kernel
theorem PrimData27.q30 : PrimData27.s30.bok = true := by decide +kernel
theorem PrimData27.q31 : PrimData27.s31.bok = true := by decide +kernel
theorem PrimData27.q32 : PrimData27.s32.bok = true := by decide +kernel
theorem PrimData27.q33 : PrimData27.s33.bok = true := by decide +kernel
theorem PrimData27.q34 : PrimData27.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData27.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData27.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData27.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData27.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData27.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
