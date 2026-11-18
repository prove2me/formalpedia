-- Prove2me | solution 1 for PrimorialCert.block_25
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:42.851969+00:00
-- url     : https://prove2.me/submissions/fc226d1d-83b7-48b7-9b1b-549acf8a47ee

import Definitions.Def_PrimorialCertData_25

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData25.q0 : PrimData25.s0.bok = true := by decide +kernel
theorem PrimData25.q1 : PrimData25.s1.bok = true := by decide +kernel
theorem PrimData25.q2 : PrimData25.s2.bok = true := by decide +kernel
theorem PrimData25.q3 : PrimData25.s3.bok = true := by decide +kernel
theorem PrimData25.q4 : PrimData25.s4.bok = true := by decide +kernel
theorem PrimData25.q5 : PrimData25.s5.bok = true := by decide +kernel
theorem PrimData25.q6 : PrimData25.s6.bok = true := by decide +kernel
theorem PrimData25.q7 : PrimData25.s7.bok = true := by decide +kernel
theorem PrimData25.q8 : PrimData25.s8.bok = true := by decide +kernel
theorem PrimData25.q9 : PrimData25.s9.bok = true := by decide +kernel
theorem PrimData25.q10 : PrimData25.s10.bok = true := by decide +kernel
theorem PrimData25.q11 : PrimData25.s11.bok = true := by decide +kernel
theorem PrimData25.q12 : PrimData25.s12.bok = true := by decide +kernel
theorem PrimData25.q13 : PrimData25.s13.bok = true := by decide +kernel
theorem PrimData25.q14 : PrimData25.s14.bok = true := by decide +kernel
theorem PrimData25.q15 : PrimData25.s15.bok = true := by decide +kernel
theorem PrimData25.q16 : PrimData25.s16.bok = true := by decide +kernel
theorem PrimData25.q17 : PrimData25.s17.bok = true := by decide +kernel
theorem PrimData25.q18 : PrimData25.s18.bok = true := by decide +kernel
theorem PrimData25.q19 : PrimData25.s19.bok = true := by decide +kernel
theorem PrimData25.q20 : PrimData25.s20.bok = true := by decide +kernel
theorem PrimData25.q21 : PrimData25.s21.bok = true := by decide +kernel
theorem PrimData25.q22 : PrimData25.s22.bok = true := by decide +kernel
theorem PrimData25.q23 : PrimData25.s23.bok = true := by decide +kernel
theorem PrimData25.q24 : PrimData25.s24.bok = true := by decide +kernel
theorem PrimData25.q25 : PrimData25.s25.bok = true := by decide +kernel
theorem PrimData25.q26 : PrimData25.s26.bok = true := by decide +kernel
theorem PrimData25.q27 : PrimData25.s27.bok = true := by decide +kernel
theorem PrimData25.q28 : PrimData25.s28.bok = true := by decide +kernel
theorem PrimData25.q29 : PrimData25.s29.bok = true := by decide +kernel
theorem PrimData25.q30 : PrimData25.s30.bok = true := by decide +kernel
theorem PrimData25.q31 : PrimData25.s31.bok = true := by decide +kernel
theorem PrimData25.q32 : PrimData25.s32.bok = true := by decide +kernel
theorem PrimData25.q33 : PrimData25.s33.bok = true := by decide +kernel
theorem PrimData25.q34 : PrimData25.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData25.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData25.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData25.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData25.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData25.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
