-- Prove2me | solution 1 for PrimorialCert.block_28
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:48.802851+00:00
-- url     : https://prove2.me/submissions/4875193f-dfbd-47e8-bd26-7532d971e4f8

import Definitions.Def_PrimorialCertData_28

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData28.q0 : PrimData28.s0.bok = true := by decide +kernel
theorem PrimData28.q1 : PrimData28.s1.bok = true := by decide +kernel
theorem PrimData28.q2 : PrimData28.s2.bok = true := by decide +kernel
theorem PrimData28.q3 : PrimData28.s3.bok = true := by decide +kernel
theorem PrimData28.q4 : PrimData28.s4.bok = true := by decide +kernel
theorem PrimData28.q5 : PrimData28.s5.bok = true := by decide +kernel
theorem PrimData28.q6 : PrimData28.s6.bok = true := by decide +kernel
theorem PrimData28.q7 : PrimData28.s7.bok = true := by decide +kernel
theorem PrimData28.q8 : PrimData28.s8.bok = true := by decide +kernel
theorem PrimData28.q9 : PrimData28.s9.bok = true := by decide +kernel
theorem PrimData28.q10 : PrimData28.s10.bok = true := by decide +kernel
theorem PrimData28.q11 : PrimData28.s11.bok = true := by decide +kernel
theorem PrimData28.q12 : PrimData28.s12.bok = true := by decide +kernel
theorem PrimData28.q13 : PrimData28.s13.bok = true := by decide +kernel
theorem PrimData28.q14 : PrimData28.s14.bok = true := by decide +kernel
theorem PrimData28.q15 : PrimData28.s15.bok = true := by decide +kernel
theorem PrimData28.q16 : PrimData28.s16.bok = true := by decide +kernel
theorem PrimData28.q17 : PrimData28.s17.bok = true := by decide +kernel
theorem PrimData28.q18 : PrimData28.s18.bok = true := by decide +kernel
theorem PrimData28.q19 : PrimData28.s19.bok = true := by decide +kernel
theorem PrimData28.q20 : PrimData28.s20.bok = true := by decide +kernel
theorem PrimData28.q21 : PrimData28.s21.bok = true := by decide +kernel
theorem PrimData28.q22 : PrimData28.s22.bok = true := by decide +kernel
theorem PrimData28.q23 : PrimData28.s23.bok = true := by decide +kernel
theorem PrimData28.q24 : PrimData28.s24.bok = true := by decide +kernel
theorem PrimData28.q25 : PrimData28.s25.bok = true := by decide +kernel
theorem PrimData28.q26 : PrimData28.s26.bok = true := by decide +kernel
theorem PrimData28.q27 : PrimData28.s27.bok = true := by decide +kernel
theorem PrimData28.q28 : PrimData28.s28.bok = true := by decide +kernel
theorem PrimData28.q29 : PrimData28.s29.bok = true := by decide +kernel
theorem PrimData28.q30 : PrimData28.s30.bok = true := by decide +kernel
theorem PrimData28.q31 : PrimData28.s31.bok = true := by decide +kernel
theorem PrimData28.q32 : PrimData28.s32.bok = true := by decide +kernel
theorem PrimData28.q33 : PrimData28.s33.bok = true := by decide +kernel
theorem PrimData28.q34 : PrimData28.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData28.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData28.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData28.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData28.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData28.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
