-- Prove2me | solution 1 for PrimorialCert.block_42
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:15.186585+00:00
-- url     : https://prove2.me/submissions/fa749780-d061-4db9-a8c1-c2bc174c4389

import Definitions.Def_PrimorialCertData_42

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData42.q0 : PrimData42.s0.bok = true := by decide +kernel
theorem PrimData42.q1 : PrimData42.s1.bok = true := by decide +kernel
theorem PrimData42.q2 : PrimData42.s2.bok = true := by decide +kernel
theorem PrimData42.q3 : PrimData42.s3.bok = true := by decide +kernel
theorem PrimData42.q4 : PrimData42.s4.bok = true := by decide +kernel
theorem PrimData42.q5 : PrimData42.s5.bok = true := by decide +kernel
theorem PrimData42.q6 : PrimData42.s6.bok = true := by decide +kernel
theorem PrimData42.q7 : PrimData42.s7.bok = true := by decide +kernel
theorem PrimData42.q8 : PrimData42.s8.bok = true := by decide +kernel
theorem PrimData42.q9 : PrimData42.s9.bok = true := by decide +kernel
theorem PrimData42.q10 : PrimData42.s10.bok = true := by decide +kernel
theorem PrimData42.q11 : PrimData42.s11.bok = true := by decide +kernel
theorem PrimData42.q12 : PrimData42.s12.bok = true := by decide +kernel
theorem PrimData42.q13 : PrimData42.s13.bok = true := by decide +kernel
theorem PrimData42.q14 : PrimData42.s14.bok = true := by decide +kernel
theorem PrimData42.q15 : PrimData42.s15.bok = true := by decide +kernel
theorem PrimData42.q16 : PrimData42.s16.bok = true := by decide +kernel
theorem PrimData42.q17 : PrimData42.s17.bok = true := by decide +kernel
theorem PrimData42.q18 : PrimData42.s18.bok = true := by decide +kernel
theorem PrimData42.q19 : PrimData42.s19.bok = true := by decide +kernel
theorem PrimData42.q20 : PrimData42.s20.bok = true := by decide +kernel
theorem PrimData42.q21 : PrimData42.s21.bok = true := by decide +kernel
theorem PrimData42.q22 : PrimData42.s22.bok = true := by decide +kernel
theorem PrimData42.q23 : PrimData42.s23.bok = true := by decide +kernel
theorem PrimData42.q24 : PrimData42.s24.bok = true := by decide +kernel
theorem PrimData42.q25 : PrimData42.s25.bok = true := by decide +kernel
theorem PrimData42.q26 : PrimData42.s26.bok = true := by decide +kernel
theorem PrimData42.q27 : PrimData42.s27.bok = true := by decide +kernel
theorem PrimData42.q28 : PrimData42.s28.bok = true := by decide +kernel
theorem PrimData42.q29 : PrimData42.s29.bok = true := by decide +kernel
theorem PrimData42.q30 : PrimData42.s30.bok = true := by decide +kernel
theorem PrimData42.q31 : PrimData42.s31.bok = true := by decide +kernel
theorem PrimData42.q32 : PrimData42.s32.bok = true := by decide +kernel
theorem PrimData42.q33 : PrimData42.s33.bok = true := by decide +kernel
theorem PrimData42.q34 : PrimData42.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData42.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData42.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData42.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData42.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData42.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
