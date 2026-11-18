-- Prove2me | solution 1 for PrimorialCert.block_71
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:13.196205+00:00
-- url     : https://prove2.me/submissions/852d3130-a8f4-45d0-9fd2-79c71d10161f

import Definitions.Def_PrimorialCertData_71

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData71.q0 : PrimData71.s0.bok = true := by decide +kernel
theorem PrimData71.q1 : PrimData71.s1.bok = true := by decide +kernel
theorem PrimData71.q2 : PrimData71.s2.bok = true := by decide +kernel
theorem PrimData71.q3 : PrimData71.s3.bok = true := by decide +kernel
theorem PrimData71.q4 : PrimData71.s4.bok = true := by decide +kernel
theorem PrimData71.q5 : PrimData71.s5.bok = true := by decide +kernel
theorem PrimData71.q6 : PrimData71.s6.bok = true := by decide +kernel
theorem PrimData71.q7 : PrimData71.s7.bok = true := by decide +kernel
theorem PrimData71.q8 : PrimData71.s8.bok = true := by decide +kernel
theorem PrimData71.q9 : PrimData71.s9.bok = true := by decide +kernel
theorem PrimData71.q10 : PrimData71.s10.bok = true := by decide +kernel
theorem PrimData71.q11 : PrimData71.s11.bok = true := by decide +kernel
theorem PrimData71.q12 : PrimData71.s12.bok = true := by decide +kernel
theorem PrimData71.q13 : PrimData71.s13.bok = true := by decide +kernel
theorem PrimData71.q14 : PrimData71.s14.bok = true := by decide +kernel
theorem PrimData71.q15 : PrimData71.s15.bok = true := by decide +kernel
theorem PrimData71.q16 : PrimData71.s16.bok = true := by decide +kernel
theorem PrimData71.q17 : PrimData71.s17.bok = true := by decide +kernel
theorem PrimData71.q18 : PrimData71.s18.bok = true := by decide +kernel
theorem PrimData71.q19 : PrimData71.s19.bok = true := by decide +kernel
theorem PrimData71.q20 : PrimData71.s20.bok = true := by decide +kernel
theorem PrimData71.q21 : PrimData71.s21.bok = true := by decide +kernel
theorem PrimData71.q22 : PrimData71.s22.bok = true := by decide +kernel
theorem PrimData71.q23 : PrimData71.s23.bok = true := by decide +kernel
theorem PrimData71.q24 : PrimData71.s24.bok = true := by decide +kernel
theorem PrimData71.q25 : PrimData71.s25.bok = true := by decide +kernel
theorem PrimData71.q26 : PrimData71.s26.bok = true := by decide +kernel
theorem PrimData71.q27 : PrimData71.s27.bok = true := by decide +kernel
theorem PrimData71.q28 : PrimData71.s28.bok = true := by decide +kernel
theorem PrimData71.q29 : PrimData71.s29.bok = true := by decide +kernel
theorem PrimData71.q30 : PrimData71.s30.bok = true := by decide +kernel
theorem PrimData71.q31 : PrimData71.s31.bok = true := by decide +kernel
theorem PrimData71.q32 : PrimData71.s32.bok = true := by decide +kernel
theorem PrimData71.q33 : PrimData71.s33.bok = true := by decide +kernel
theorem PrimData71.q34 : PrimData71.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData71.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData71.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData71.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData71.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData71.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
