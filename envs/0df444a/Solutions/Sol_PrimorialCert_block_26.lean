-- Prove2me | solution 1 for PrimorialCert.block_26
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:44.83502+00:00
-- url     : https://prove2.me/submissions/1a52e78e-f4c0-4e1a-b19d-186d8225b534

import Definitions.Def_PrimorialCertData_26

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData26.q0 : PrimData26.s0.bok = true := by decide +kernel
theorem PrimData26.q1 : PrimData26.s1.bok = true := by decide +kernel
theorem PrimData26.q2 : PrimData26.s2.bok = true := by decide +kernel
theorem PrimData26.q3 : PrimData26.s3.bok = true := by decide +kernel
theorem PrimData26.q4 : PrimData26.s4.bok = true := by decide +kernel
theorem PrimData26.q5 : PrimData26.s5.bok = true := by decide +kernel
theorem PrimData26.q6 : PrimData26.s6.bok = true := by decide +kernel
theorem PrimData26.q7 : PrimData26.s7.bok = true := by decide +kernel
theorem PrimData26.q8 : PrimData26.s8.bok = true := by decide +kernel
theorem PrimData26.q9 : PrimData26.s9.bok = true := by decide +kernel
theorem PrimData26.q10 : PrimData26.s10.bok = true := by decide +kernel
theorem PrimData26.q11 : PrimData26.s11.bok = true := by decide +kernel
theorem PrimData26.q12 : PrimData26.s12.bok = true := by decide +kernel
theorem PrimData26.q13 : PrimData26.s13.bok = true := by decide +kernel
theorem PrimData26.q14 : PrimData26.s14.bok = true := by decide +kernel
theorem PrimData26.q15 : PrimData26.s15.bok = true := by decide +kernel
theorem PrimData26.q16 : PrimData26.s16.bok = true := by decide +kernel
theorem PrimData26.q17 : PrimData26.s17.bok = true := by decide +kernel
theorem PrimData26.q18 : PrimData26.s18.bok = true := by decide +kernel
theorem PrimData26.q19 : PrimData26.s19.bok = true := by decide +kernel
theorem PrimData26.q20 : PrimData26.s20.bok = true := by decide +kernel
theorem PrimData26.q21 : PrimData26.s21.bok = true := by decide +kernel
theorem PrimData26.q22 : PrimData26.s22.bok = true := by decide +kernel
theorem PrimData26.q23 : PrimData26.s23.bok = true := by decide +kernel
theorem PrimData26.q24 : PrimData26.s24.bok = true := by decide +kernel
theorem PrimData26.q25 : PrimData26.s25.bok = true := by decide +kernel
theorem PrimData26.q26 : PrimData26.s26.bok = true := by decide +kernel
theorem PrimData26.q27 : PrimData26.s27.bok = true := by decide +kernel
theorem PrimData26.q28 : PrimData26.s28.bok = true := by decide +kernel
theorem PrimData26.q29 : PrimData26.s29.bok = true := by decide +kernel
theorem PrimData26.q30 : PrimData26.s30.bok = true := by decide +kernel
theorem PrimData26.q31 : PrimData26.s31.bok = true := by decide +kernel
theorem PrimData26.q32 : PrimData26.s32.bok = true := by decide +kernel
theorem PrimData26.q33 : PrimData26.s33.bok = true := by decide +kernel
theorem PrimData26.q34 : PrimData26.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData26.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData26.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData26.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData26.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData26.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
