-- Prove2me | solution 1 for PrimorialCert.block_47
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:25.074672+00:00
-- url     : https://prove2.me/submissions/8385d845-2e00-4f5b-8315-4e601520823c

import Definitions.Def_PrimorialCertData_47

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData47.q0 : PrimData47.s0.bok = true := by decide +kernel
theorem PrimData47.q1 : PrimData47.s1.bok = true := by decide +kernel
theorem PrimData47.q2 : PrimData47.s2.bok = true := by decide +kernel
theorem PrimData47.q3 : PrimData47.s3.bok = true := by decide +kernel
theorem PrimData47.q4 : PrimData47.s4.bok = true := by decide +kernel
theorem PrimData47.q5 : PrimData47.s5.bok = true := by decide +kernel
theorem PrimData47.q6 : PrimData47.s6.bok = true := by decide +kernel
theorem PrimData47.q7 : PrimData47.s7.bok = true := by decide +kernel
theorem PrimData47.q8 : PrimData47.s8.bok = true := by decide +kernel
theorem PrimData47.q9 : PrimData47.s9.bok = true := by decide +kernel
theorem PrimData47.q10 : PrimData47.s10.bok = true := by decide +kernel
theorem PrimData47.q11 : PrimData47.s11.bok = true := by decide +kernel
theorem PrimData47.q12 : PrimData47.s12.bok = true := by decide +kernel
theorem PrimData47.q13 : PrimData47.s13.bok = true := by decide +kernel
theorem PrimData47.q14 : PrimData47.s14.bok = true := by decide +kernel
theorem PrimData47.q15 : PrimData47.s15.bok = true := by decide +kernel
theorem PrimData47.q16 : PrimData47.s16.bok = true := by decide +kernel
theorem PrimData47.q17 : PrimData47.s17.bok = true := by decide +kernel
theorem PrimData47.q18 : PrimData47.s18.bok = true := by decide +kernel
theorem PrimData47.q19 : PrimData47.s19.bok = true := by decide +kernel
theorem PrimData47.q20 : PrimData47.s20.bok = true := by decide +kernel
theorem PrimData47.q21 : PrimData47.s21.bok = true := by decide +kernel
theorem PrimData47.q22 : PrimData47.s22.bok = true := by decide +kernel
theorem PrimData47.q23 : PrimData47.s23.bok = true := by decide +kernel
theorem PrimData47.q24 : PrimData47.s24.bok = true := by decide +kernel
theorem PrimData47.q25 : PrimData47.s25.bok = true := by decide +kernel
theorem PrimData47.q26 : PrimData47.s26.bok = true := by decide +kernel
theorem PrimData47.q27 : PrimData47.s27.bok = true := by decide +kernel
theorem PrimData47.q28 : PrimData47.s28.bok = true := by decide +kernel
theorem PrimData47.q29 : PrimData47.s29.bok = true := by decide +kernel
theorem PrimData47.q30 : PrimData47.s30.bok = true := by decide +kernel
theorem PrimData47.q31 : PrimData47.s31.bok = true := by decide +kernel
theorem PrimData47.q32 : PrimData47.s32.bok = true := by decide +kernel
theorem PrimData47.q33 : PrimData47.s33.bok = true := by decide +kernel
theorem PrimData47.q34 : PrimData47.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData47.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData47.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData47.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData47.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData47.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
