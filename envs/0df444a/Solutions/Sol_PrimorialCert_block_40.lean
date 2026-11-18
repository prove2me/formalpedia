-- Prove2me | solution 1 for PrimorialCert.block_40
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:12:46.301066+00:00
-- url     : https://prove2.me/submissions/2e355076-163c-44e2-b5f9-be6c1ac644f6

import Definitions.Def_PrimorialCertData_40

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData40.q0 : PrimData40.s0.bok = true := by decide +kernel
theorem PrimData40.q1 : PrimData40.s1.bok = true := by decide +kernel
theorem PrimData40.q2 : PrimData40.s2.bok = true := by decide +kernel
theorem PrimData40.q3 : PrimData40.s3.bok = true := by decide +kernel
theorem PrimData40.q4 : PrimData40.s4.bok = true := by decide +kernel
theorem PrimData40.q5 : PrimData40.s5.bok = true := by decide +kernel
theorem PrimData40.q6 : PrimData40.s6.bok = true := by decide +kernel
theorem PrimData40.q7 : PrimData40.s7.bok = true := by decide +kernel
theorem PrimData40.q8 : PrimData40.s8.bok = true := by decide +kernel
theorem PrimData40.q9 : PrimData40.s9.bok = true := by decide +kernel
theorem PrimData40.q10 : PrimData40.s10.bok = true := by decide +kernel
theorem PrimData40.q11 : PrimData40.s11.bok = true := by decide +kernel
theorem PrimData40.q12 : PrimData40.s12.bok = true := by decide +kernel
theorem PrimData40.q13 : PrimData40.s13.bok = true := by decide +kernel
theorem PrimData40.q14 : PrimData40.s14.bok = true := by decide +kernel
theorem PrimData40.q15 : PrimData40.s15.bok = true := by decide +kernel
theorem PrimData40.q16 : PrimData40.s16.bok = true := by decide +kernel
theorem PrimData40.q17 : PrimData40.s17.bok = true := by decide +kernel
theorem PrimData40.q18 : PrimData40.s18.bok = true := by decide +kernel
theorem PrimData40.q19 : PrimData40.s19.bok = true := by decide +kernel
theorem PrimData40.q20 : PrimData40.s20.bok = true := by decide +kernel
theorem PrimData40.q21 : PrimData40.s21.bok = true := by decide +kernel
theorem PrimData40.q22 : PrimData40.s22.bok = true := by decide +kernel
theorem PrimData40.q23 : PrimData40.s23.bok = true := by decide +kernel
theorem PrimData40.q24 : PrimData40.s24.bok = true := by decide +kernel
theorem PrimData40.q25 : PrimData40.s25.bok = true := by decide +kernel
theorem PrimData40.q26 : PrimData40.s26.bok = true := by decide +kernel
theorem PrimData40.q27 : PrimData40.s27.bok = true := by decide +kernel
theorem PrimData40.q28 : PrimData40.s28.bok = true := by decide +kernel
theorem PrimData40.q29 : PrimData40.s29.bok = true := by decide +kernel
theorem PrimData40.q30 : PrimData40.s30.bok = true := by decide +kernel
theorem PrimData40.q31 : PrimData40.s31.bok = true := by decide +kernel
theorem PrimData40.q32 : PrimData40.s32.bok = true := by decide +kernel
theorem PrimData40.q33 : PrimData40.s33.bok = true := by decide +kernel
theorem PrimData40.q34 : PrimData40.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData40.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData40.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData40.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData40.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData40.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
