-- Prove2me | solution 1 for PrimorialCert.block_58
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:47.149786+00:00
-- url     : https://prove2.me/submissions/9eab480f-b0bc-4c38-a1f6-8a8882337934

import Definitions.Def_PrimorialCertData_58

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData58.q0 : PrimData58.s0.bok = true := by decide +kernel
theorem PrimData58.q1 : PrimData58.s1.bok = true := by decide +kernel
theorem PrimData58.q2 : PrimData58.s2.bok = true := by decide +kernel
theorem PrimData58.q3 : PrimData58.s3.bok = true := by decide +kernel
theorem PrimData58.q4 : PrimData58.s4.bok = true := by decide +kernel
theorem PrimData58.q5 : PrimData58.s5.bok = true := by decide +kernel
theorem PrimData58.q6 : PrimData58.s6.bok = true := by decide +kernel
theorem PrimData58.q7 : PrimData58.s7.bok = true := by decide +kernel
theorem PrimData58.q8 : PrimData58.s8.bok = true := by decide +kernel
theorem PrimData58.q9 : PrimData58.s9.bok = true := by decide +kernel
theorem PrimData58.q10 : PrimData58.s10.bok = true := by decide +kernel
theorem PrimData58.q11 : PrimData58.s11.bok = true := by decide +kernel
theorem PrimData58.q12 : PrimData58.s12.bok = true := by decide +kernel
theorem PrimData58.q13 : PrimData58.s13.bok = true := by decide +kernel
theorem PrimData58.q14 : PrimData58.s14.bok = true := by decide +kernel
theorem PrimData58.q15 : PrimData58.s15.bok = true := by decide +kernel
theorem PrimData58.q16 : PrimData58.s16.bok = true := by decide +kernel
theorem PrimData58.q17 : PrimData58.s17.bok = true := by decide +kernel
theorem PrimData58.q18 : PrimData58.s18.bok = true := by decide +kernel
theorem PrimData58.q19 : PrimData58.s19.bok = true := by decide +kernel
theorem PrimData58.q20 : PrimData58.s20.bok = true := by decide +kernel
theorem PrimData58.q21 : PrimData58.s21.bok = true := by decide +kernel
theorem PrimData58.q22 : PrimData58.s22.bok = true := by decide +kernel
theorem PrimData58.q23 : PrimData58.s23.bok = true := by decide +kernel
theorem PrimData58.q24 : PrimData58.s24.bok = true := by decide +kernel
theorem PrimData58.q25 : PrimData58.s25.bok = true := by decide +kernel
theorem PrimData58.q26 : PrimData58.s26.bok = true := by decide +kernel
theorem PrimData58.q27 : PrimData58.s27.bok = true := by decide +kernel
theorem PrimData58.q28 : PrimData58.s28.bok = true := by decide +kernel
theorem PrimData58.q29 : PrimData58.s29.bok = true := by decide +kernel
theorem PrimData58.q30 : PrimData58.s30.bok = true := by decide +kernel
theorem PrimData58.q31 : PrimData58.s31.bok = true := by decide +kernel
theorem PrimData58.q32 : PrimData58.s32.bok = true := by decide +kernel
theorem PrimData58.q33 : PrimData58.s33.bok = true := by decide +kernel
theorem PrimData58.q34 : PrimData58.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData58.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData58.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData58.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData58.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData58.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
