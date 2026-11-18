-- Prove2me | solution 1 for PrimorialCert.block_66
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:03.308333+00:00
-- url     : https://prove2.me/submissions/1e268014-b462-4ee7-b455-02f8d0535763

import Definitions.Def_PrimorialCertData_66

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData66.q0 : PrimData66.s0.bok = true := by decide +kernel
theorem PrimData66.q1 : PrimData66.s1.bok = true := by decide +kernel
theorem PrimData66.q2 : PrimData66.s2.bok = true := by decide +kernel
theorem PrimData66.q3 : PrimData66.s3.bok = true := by decide +kernel
theorem PrimData66.q4 : PrimData66.s4.bok = true := by decide +kernel
theorem PrimData66.q5 : PrimData66.s5.bok = true := by decide +kernel
theorem PrimData66.q6 : PrimData66.s6.bok = true := by decide +kernel
theorem PrimData66.q7 : PrimData66.s7.bok = true := by decide +kernel
theorem PrimData66.q8 : PrimData66.s8.bok = true := by decide +kernel
theorem PrimData66.q9 : PrimData66.s9.bok = true := by decide +kernel
theorem PrimData66.q10 : PrimData66.s10.bok = true := by decide +kernel
theorem PrimData66.q11 : PrimData66.s11.bok = true := by decide +kernel
theorem PrimData66.q12 : PrimData66.s12.bok = true := by decide +kernel
theorem PrimData66.q13 : PrimData66.s13.bok = true := by decide +kernel
theorem PrimData66.q14 : PrimData66.s14.bok = true := by decide +kernel
theorem PrimData66.q15 : PrimData66.s15.bok = true := by decide +kernel
theorem PrimData66.q16 : PrimData66.s16.bok = true := by decide +kernel
theorem PrimData66.q17 : PrimData66.s17.bok = true := by decide +kernel
theorem PrimData66.q18 : PrimData66.s18.bok = true := by decide +kernel
theorem PrimData66.q19 : PrimData66.s19.bok = true := by decide +kernel
theorem PrimData66.q20 : PrimData66.s20.bok = true := by decide +kernel
theorem PrimData66.q21 : PrimData66.s21.bok = true := by decide +kernel
theorem PrimData66.q22 : PrimData66.s22.bok = true := by decide +kernel
theorem PrimData66.q23 : PrimData66.s23.bok = true := by decide +kernel
theorem PrimData66.q24 : PrimData66.s24.bok = true := by decide +kernel
theorem PrimData66.q25 : PrimData66.s25.bok = true := by decide +kernel
theorem PrimData66.q26 : PrimData66.s26.bok = true := by decide +kernel
theorem PrimData66.q27 : PrimData66.s27.bok = true := by decide +kernel
theorem PrimData66.q28 : PrimData66.s28.bok = true := by decide +kernel
theorem PrimData66.q29 : PrimData66.s29.bok = true := by decide +kernel
theorem PrimData66.q30 : PrimData66.s30.bok = true := by decide +kernel
theorem PrimData66.q31 : PrimData66.s31.bok = true := by decide +kernel
theorem PrimData66.q32 : PrimData66.s32.bok = true := by decide +kernel
theorem PrimData66.q33 : PrimData66.s33.bok = true := by decide +kernel
theorem PrimData66.q34 : PrimData66.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData66.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData66.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData66.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData66.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData66.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
