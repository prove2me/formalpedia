-- Prove2me | solution 1 for PrimorialCert.block_32
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:56.873099+00:00
-- url     : https://prove2.me/submissions/52c508d4-9135-42e4-98f3-2e45bfa8db75

import Definitions.Def_PrimorialCertData_32

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData32.q0 : PrimData32.s0.bok = true := by decide +kernel
theorem PrimData32.q1 : PrimData32.s1.bok = true := by decide +kernel
theorem PrimData32.q2 : PrimData32.s2.bok = true := by decide +kernel
theorem PrimData32.q3 : PrimData32.s3.bok = true := by decide +kernel
theorem PrimData32.q4 : PrimData32.s4.bok = true := by decide +kernel
theorem PrimData32.q5 : PrimData32.s5.bok = true := by decide +kernel
theorem PrimData32.q6 : PrimData32.s6.bok = true := by decide +kernel
theorem PrimData32.q7 : PrimData32.s7.bok = true := by decide +kernel
theorem PrimData32.q8 : PrimData32.s8.bok = true := by decide +kernel
theorem PrimData32.q9 : PrimData32.s9.bok = true := by decide +kernel
theorem PrimData32.q10 : PrimData32.s10.bok = true := by decide +kernel
theorem PrimData32.q11 : PrimData32.s11.bok = true := by decide +kernel
theorem PrimData32.q12 : PrimData32.s12.bok = true := by decide +kernel
theorem PrimData32.q13 : PrimData32.s13.bok = true := by decide +kernel
theorem PrimData32.q14 : PrimData32.s14.bok = true := by decide +kernel
theorem PrimData32.q15 : PrimData32.s15.bok = true := by decide +kernel
theorem PrimData32.q16 : PrimData32.s16.bok = true := by decide +kernel
theorem PrimData32.q17 : PrimData32.s17.bok = true := by decide +kernel
theorem PrimData32.q18 : PrimData32.s18.bok = true := by decide +kernel
theorem PrimData32.q19 : PrimData32.s19.bok = true := by decide +kernel
theorem PrimData32.q20 : PrimData32.s20.bok = true := by decide +kernel
theorem PrimData32.q21 : PrimData32.s21.bok = true := by decide +kernel
theorem PrimData32.q22 : PrimData32.s22.bok = true := by decide +kernel
theorem PrimData32.q23 : PrimData32.s23.bok = true := by decide +kernel
theorem PrimData32.q24 : PrimData32.s24.bok = true := by decide +kernel
theorem PrimData32.q25 : PrimData32.s25.bok = true := by decide +kernel
theorem PrimData32.q26 : PrimData32.s26.bok = true := by decide +kernel
theorem PrimData32.q27 : PrimData32.s27.bok = true := by decide +kernel
theorem PrimData32.q28 : PrimData32.s28.bok = true := by decide +kernel
theorem PrimData32.q29 : PrimData32.s29.bok = true := by decide +kernel
theorem PrimData32.q30 : PrimData32.s30.bok = true := by decide +kernel
theorem PrimData32.q31 : PrimData32.s31.bok = true := by decide +kernel
theorem PrimData32.q32 : PrimData32.s32.bok = true := by decide +kernel
theorem PrimData32.q33 : PrimData32.s33.bok = true := by decide +kernel
theorem PrimData32.q34 : PrimData32.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData32.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData32.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData32.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData32.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData32.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
