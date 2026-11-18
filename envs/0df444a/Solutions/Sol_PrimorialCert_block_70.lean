-- Prove2me | solution 1 for PrimorialCert.block_70
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:11.244175+00:00
-- url     : https://prove2.me/submissions/9354dc4b-574e-402b-99c1-9a18bf4275ed

import Definitions.Def_PrimorialCertData_70

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData70.q0 : PrimData70.s0.bok = true := by decide +kernel
theorem PrimData70.q1 : PrimData70.s1.bok = true := by decide +kernel
theorem PrimData70.q2 : PrimData70.s2.bok = true := by decide +kernel
theorem PrimData70.q3 : PrimData70.s3.bok = true := by decide +kernel
theorem PrimData70.q4 : PrimData70.s4.bok = true := by decide +kernel
theorem PrimData70.q5 : PrimData70.s5.bok = true := by decide +kernel
theorem PrimData70.q6 : PrimData70.s6.bok = true := by decide +kernel
theorem PrimData70.q7 : PrimData70.s7.bok = true := by decide +kernel
theorem PrimData70.q8 : PrimData70.s8.bok = true := by decide +kernel
theorem PrimData70.q9 : PrimData70.s9.bok = true := by decide +kernel
theorem PrimData70.q10 : PrimData70.s10.bok = true := by decide +kernel
theorem PrimData70.q11 : PrimData70.s11.bok = true := by decide +kernel
theorem PrimData70.q12 : PrimData70.s12.bok = true := by decide +kernel
theorem PrimData70.q13 : PrimData70.s13.bok = true := by decide +kernel
theorem PrimData70.q14 : PrimData70.s14.bok = true := by decide +kernel
theorem PrimData70.q15 : PrimData70.s15.bok = true := by decide +kernel
theorem PrimData70.q16 : PrimData70.s16.bok = true := by decide +kernel
theorem PrimData70.q17 : PrimData70.s17.bok = true := by decide +kernel
theorem PrimData70.q18 : PrimData70.s18.bok = true := by decide +kernel
theorem PrimData70.q19 : PrimData70.s19.bok = true := by decide +kernel
theorem PrimData70.q20 : PrimData70.s20.bok = true := by decide +kernel
theorem PrimData70.q21 : PrimData70.s21.bok = true := by decide +kernel
theorem PrimData70.q22 : PrimData70.s22.bok = true := by decide +kernel
theorem PrimData70.q23 : PrimData70.s23.bok = true := by decide +kernel
theorem PrimData70.q24 : PrimData70.s24.bok = true := by decide +kernel
theorem PrimData70.q25 : PrimData70.s25.bok = true := by decide +kernel
theorem PrimData70.q26 : PrimData70.s26.bok = true := by decide +kernel
theorem PrimData70.q27 : PrimData70.s27.bok = true := by decide +kernel
theorem PrimData70.q28 : PrimData70.s28.bok = true := by decide +kernel
theorem PrimData70.q29 : PrimData70.s29.bok = true := by decide +kernel
theorem PrimData70.q30 : PrimData70.s30.bok = true := by decide +kernel
theorem PrimData70.q31 : PrimData70.s31.bok = true := by decide +kernel
theorem PrimData70.q32 : PrimData70.s32.bok = true := by decide +kernel
theorem PrimData70.q33 : PrimData70.s33.bok = true := by decide +kernel
theorem PrimData70.q34 : PrimData70.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData70.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData70.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData70.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData70.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData70.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
