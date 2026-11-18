-- Prove2me | solution 1 for PrimorialCert.block_69
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:09.23793+00:00
-- url     : https://prove2.me/submissions/e8fe09be-b696-4e50-be88-4c7627b8f6a5

import Definitions.Def_PrimorialCertData_69

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData69.q0 : PrimData69.s0.bok = true := by decide +kernel
theorem PrimData69.q1 : PrimData69.s1.bok = true := by decide +kernel
theorem PrimData69.q2 : PrimData69.s2.bok = true := by decide +kernel
theorem PrimData69.q3 : PrimData69.s3.bok = true := by decide +kernel
theorem PrimData69.q4 : PrimData69.s4.bok = true := by decide +kernel
theorem PrimData69.q5 : PrimData69.s5.bok = true := by decide +kernel
theorem PrimData69.q6 : PrimData69.s6.bok = true := by decide +kernel
theorem PrimData69.q7 : PrimData69.s7.bok = true := by decide +kernel
theorem PrimData69.q8 : PrimData69.s8.bok = true := by decide +kernel
theorem PrimData69.q9 : PrimData69.s9.bok = true := by decide +kernel
theorem PrimData69.q10 : PrimData69.s10.bok = true := by decide +kernel
theorem PrimData69.q11 : PrimData69.s11.bok = true := by decide +kernel
theorem PrimData69.q12 : PrimData69.s12.bok = true := by decide +kernel
theorem PrimData69.q13 : PrimData69.s13.bok = true := by decide +kernel
theorem PrimData69.q14 : PrimData69.s14.bok = true := by decide +kernel
theorem PrimData69.q15 : PrimData69.s15.bok = true := by decide +kernel
theorem PrimData69.q16 : PrimData69.s16.bok = true := by decide +kernel
theorem PrimData69.q17 : PrimData69.s17.bok = true := by decide +kernel
theorem PrimData69.q18 : PrimData69.s18.bok = true := by decide +kernel
theorem PrimData69.q19 : PrimData69.s19.bok = true := by decide +kernel
theorem PrimData69.q20 : PrimData69.s20.bok = true := by decide +kernel
theorem PrimData69.q21 : PrimData69.s21.bok = true := by decide +kernel
theorem PrimData69.q22 : PrimData69.s22.bok = true := by decide +kernel
theorem PrimData69.q23 : PrimData69.s23.bok = true := by decide +kernel
theorem PrimData69.q24 : PrimData69.s24.bok = true := by decide +kernel
theorem PrimData69.q25 : PrimData69.s25.bok = true := by decide +kernel
theorem PrimData69.q26 : PrimData69.s26.bok = true := by decide +kernel
theorem PrimData69.q27 : PrimData69.s27.bok = true := by decide +kernel
theorem PrimData69.q28 : PrimData69.s28.bok = true := by decide +kernel
theorem PrimData69.q29 : PrimData69.s29.bok = true := by decide +kernel
theorem PrimData69.q30 : PrimData69.s30.bok = true := by decide +kernel
theorem PrimData69.q31 : PrimData69.s31.bok = true := by decide +kernel
theorem PrimData69.q32 : PrimData69.s32.bok = true := by decide +kernel
theorem PrimData69.q33 : PrimData69.s33.bok = true := by decide +kernel
theorem PrimData69.q34 : PrimData69.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData69.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData69.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData69.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData69.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData69.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
