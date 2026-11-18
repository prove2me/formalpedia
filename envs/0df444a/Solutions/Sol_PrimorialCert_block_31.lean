-- Prove2me | solution 1 for PrimorialCert.block_31
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:54.904946+00:00
-- url     : https://prove2.me/submissions/d092fa51-0ac5-423d-8078-607d71f58e17

import Definitions.Def_PrimorialCertData_31

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData31.q0 : PrimData31.s0.bok = true := by decide +kernel
theorem PrimData31.q1 : PrimData31.s1.bok = true := by decide +kernel
theorem PrimData31.q2 : PrimData31.s2.bok = true := by decide +kernel
theorem PrimData31.q3 : PrimData31.s3.bok = true := by decide +kernel
theorem PrimData31.q4 : PrimData31.s4.bok = true := by decide +kernel
theorem PrimData31.q5 : PrimData31.s5.bok = true := by decide +kernel
theorem PrimData31.q6 : PrimData31.s6.bok = true := by decide +kernel
theorem PrimData31.q7 : PrimData31.s7.bok = true := by decide +kernel
theorem PrimData31.q8 : PrimData31.s8.bok = true := by decide +kernel
theorem PrimData31.q9 : PrimData31.s9.bok = true := by decide +kernel
theorem PrimData31.q10 : PrimData31.s10.bok = true := by decide +kernel
theorem PrimData31.q11 : PrimData31.s11.bok = true := by decide +kernel
theorem PrimData31.q12 : PrimData31.s12.bok = true := by decide +kernel
theorem PrimData31.q13 : PrimData31.s13.bok = true := by decide +kernel
theorem PrimData31.q14 : PrimData31.s14.bok = true := by decide +kernel
theorem PrimData31.q15 : PrimData31.s15.bok = true := by decide +kernel
theorem PrimData31.q16 : PrimData31.s16.bok = true := by decide +kernel
theorem PrimData31.q17 : PrimData31.s17.bok = true := by decide +kernel
theorem PrimData31.q18 : PrimData31.s18.bok = true := by decide +kernel
theorem PrimData31.q19 : PrimData31.s19.bok = true := by decide +kernel
theorem PrimData31.q20 : PrimData31.s20.bok = true := by decide +kernel
theorem PrimData31.q21 : PrimData31.s21.bok = true := by decide +kernel
theorem PrimData31.q22 : PrimData31.s22.bok = true := by decide +kernel
theorem PrimData31.q23 : PrimData31.s23.bok = true := by decide +kernel
theorem PrimData31.q24 : PrimData31.s24.bok = true := by decide +kernel
theorem PrimData31.q25 : PrimData31.s25.bok = true := by decide +kernel
theorem PrimData31.q26 : PrimData31.s26.bok = true := by decide +kernel
theorem PrimData31.q27 : PrimData31.s27.bok = true := by decide +kernel
theorem PrimData31.q28 : PrimData31.s28.bok = true := by decide +kernel
theorem PrimData31.q29 : PrimData31.s29.bok = true := by decide +kernel
theorem PrimData31.q30 : PrimData31.s30.bok = true := by decide +kernel
theorem PrimData31.q31 : PrimData31.s31.bok = true := by decide +kernel
theorem PrimData31.q32 : PrimData31.s32.bok = true := by decide +kernel
theorem PrimData31.q33 : PrimData31.s33.bok = true := by decide +kernel
theorem PrimData31.q34 : PrimData31.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData31.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData31.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData31.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData31.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData31.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
