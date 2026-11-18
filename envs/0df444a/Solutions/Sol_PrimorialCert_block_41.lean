-- Prove2me | solution 1 for PrimorialCert.block_41
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:12.99412+00:00
-- url     : https://prove2.me/submissions/23c4cbc3-d7c4-4c4c-86c3-0fcb8576c7e0

import Definitions.Def_PrimorialCertData_41

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData41.q0 : PrimData41.s0.bok = true := by decide +kernel
theorem PrimData41.q1 : PrimData41.s1.bok = true := by decide +kernel
theorem PrimData41.q2 : PrimData41.s2.bok = true := by decide +kernel
theorem PrimData41.q3 : PrimData41.s3.bok = true := by decide +kernel
theorem PrimData41.q4 : PrimData41.s4.bok = true := by decide +kernel
theorem PrimData41.q5 : PrimData41.s5.bok = true := by decide +kernel
theorem PrimData41.q6 : PrimData41.s6.bok = true := by decide +kernel
theorem PrimData41.q7 : PrimData41.s7.bok = true := by decide +kernel
theorem PrimData41.q8 : PrimData41.s8.bok = true := by decide +kernel
theorem PrimData41.q9 : PrimData41.s9.bok = true := by decide +kernel
theorem PrimData41.q10 : PrimData41.s10.bok = true := by decide +kernel
theorem PrimData41.q11 : PrimData41.s11.bok = true := by decide +kernel
theorem PrimData41.q12 : PrimData41.s12.bok = true := by decide +kernel
theorem PrimData41.q13 : PrimData41.s13.bok = true := by decide +kernel
theorem PrimData41.q14 : PrimData41.s14.bok = true := by decide +kernel
theorem PrimData41.q15 : PrimData41.s15.bok = true := by decide +kernel
theorem PrimData41.q16 : PrimData41.s16.bok = true := by decide +kernel
theorem PrimData41.q17 : PrimData41.s17.bok = true := by decide +kernel
theorem PrimData41.q18 : PrimData41.s18.bok = true := by decide +kernel
theorem PrimData41.q19 : PrimData41.s19.bok = true := by decide +kernel
theorem PrimData41.q20 : PrimData41.s20.bok = true := by decide +kernel
theorem PrimData41.q21 : PrimData41.s21.bok = true := by decide +kernel
theorem PrimData41.q22 : PrimData41.s22.bok = true := by decide +kernel
theorem PrimData41.q23 : PrimData41.s23.bok = true := by decide +kernel
theorem PrimData41.q24 : PrimData41.s24.bok = true := by decide +kernel
theorem PrimData41.q25 : PrimData41.s25.bok = true := by decide +kernel
theorem PrimData41.q26 : PrimData41.s26.bok = true := by decide +kernel
theorem PrimData41.q27 : PrimData41.s27.bok = true := by decide +kernel
theorem PrimData41.q28 : PrimData41.s28.bok = true := by decide +kernel
theorem PrimData41.q29 : PrimData41.s29.bok = true := by decide +kernel
theorem PrimData41.q30 : PrimData41.s30.bok = true := by decide +kernel
theorem PrimData41.q31 : PrimData41.s31.bok = true := by decide +kernel
theorem PrimData41.q32 : PrimData41.s32.bok = true := by decide +kernel
theorem PrimData41.q33 : PrimData41.s33.bok = true := by decide +kernel
theorem PrimData41.q34 : PrimData41.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData41.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData41.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData41.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData41.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData41.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
