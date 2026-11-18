-- Prove2me | solution 1 for PrimorialCert.block_29
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:50.86928+00:00
-- url     : https://prove2.me/submissions/5f7bda5e-7404-4eb4-ab59-efa5c701eeeb

import Definitions.Def_PrimorialCertData_29

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData29.q0 : PrimData29.s0.bok = true := by decide +kernel
theorem PrimData29.q1 : PrimData29.s1.bok = true := by decide +kernel
theorem PrimData29.q2 : PrimData29.s2.bok = true := by decide +kernel
theorem PrimData29.q3 : PrimData29.s3.bok = true := by decide +kernel
theorem PrimData29.q4 : PrimData29.s4.bok = true := by decide +kernel
theorem PrimData29.q5 : PrimData29.s5.bok = true := by decide +kernel
theorem PrimData29.q6 : PrimData29.s6.bok = true := by decide +kernel
theorem PrimData29.q7 : PrimData29.s7.bok = true := by decide +kernel
theorem PrimData29.q8 : PrimData29.s8.bok = true := by decide +kernel
theorem PrimData29.q9 : PrimData29.s9.bok = true := by decide +kernel
theorem PrimData29.q10 : PrimData29.s10.bok = true := by decide +kernel
theorem PrimData29.q11 : PrimData29.s11.bok = true := by decide +kernel
theorem PrimData29.q12 : PrimData29.s12.bok = true := by decide +kernel
theorem PrimData29.q13 : PrimData29.s13.bok = true := by decide +kernel
theorem PrimData29.q14 : PrimData29.s14.bok = true := by decide +kernel
theorem PrimData29.q15 : PrimData29.s15.bok = true := by decide +kernel
theorem PrimData29.q16 : PrimData29.s16.bok = true := by decide +kernel
theorem PrimData29.q17 : PrimData29.s17.bok = true := by decide +kernel
theorem PrimData29.q18 : PrimData29.s18.bok = true := by decide +kernel
theorem PrimData29.q19 : PrimData29.s19.bok = true := by decide +kernel
theorem PrimData29.q20 : PrimData29.s20.bok = true := by decide +kernel
theorem PrimData29.q21 : PrimData29.s21.bok = true := by decide +kernel
theorem PrimData29.q22 : PrimData29.s22.bok = true := by decide +kernel
theorem PrimData29.q23 : PrimData29.s23.bok = true := by decide +kernel
theorem PrimData29.q24 : PrimData29.s24.bok = true := by decide +kernel
theorem PrimData29.q25 : PrimData29.s25.bok = true := by decide +kernel
theorem PrimData29.q26 : PrimData29.s26.bok = true := by decide +kernel
theorem PrimData29.q27 : PrimData29.s27.bok = true := by decide +kernel
theorem PrimData29.q28 : PrimData29.s28.bok = true := by decide +kernel
theorem PrimData29.q29 : PrimData29.s29.bok = true := by decide +kernel
theorem PrimData29.q30 : PrimData29.s30.bok = true := by decide +kernel
theorem PrimData29.q31 : PrimData29.s31.bok = true := by decide +kernel
theorem PrimData29.q32 : PrimData29.s32.bok = true := by decide +kernel
theorem PrimData29.q33 : PrimData29.s33.bok = true := by decide +kernel
theorem PrimData29.q34 : PrimData29.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData29.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData29.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData29.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData29.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData29.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
