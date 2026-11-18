-- Prove2me | solution 1 for PrimorialCert.block_50
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:31.062418+00:00
-- url     : https://prove2.me/submissions/0215385e-66da-4a60-9c90-1627aa5e307c

import Definitions.Def_PrimorialCertData_50

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData50.q0 : PrimData50.s0.bok = true := by decide +kernel
theorem PrimData50.q1 : PrimData50.s1.bok = true := by decide +kernel
theorem PrimData50.q2 : PrimData50.s2.bok = true := by decide +kernel
theorem PrimData50.q3 : PrimData50.s3.bok = true := by decide +kernel
theorem PrimData50.q4 : PrimData50.s4.bok = true := by decide +kernel
theorem PrimData50.q5 : PrimData50.s5.bok = true := by decide +kernel
theorem PrimData50.q6 : PrimData50.s6.bok = true := by decide +kernel
theorem PrimData50.q7 : PrimData50.s7.bok = true := by decide +kernel
theorem PrimData50.q8 : PrimData50.s8.bok = true := by decide +kernel
theorem PrimData50.q9 : PrimData50.s9.bok = true := by decide +kernel
theorem PrimData50.q10 : PrimData50.s10.bok = true := by decide +kernel
theorem PrimData50.q11 : PrimData50.s11.bok = true := by decide +kernel
theorem PrimData50.q12 : PrimData50.s12.bok = true := by decide +kernel
theorem PrimData50.q13 : PrimData50.s13.bok = true := by decide +kernel
theorem PrimData50.q14 : PrimData50.s14.bok = true := by decide +kernel
theorem PrimData50.q15 : PrimData50.s15.bok = true := by decide +kernel
theorem PrimData50.q16 : PrimData50.s16.bok = true := by decide +kernel
theorem PrimData50.q17 : PrimData50.s17.bok = true := by decide +kernel
theorem PrimData50.q18 : PrimData50.s18.bok = true := by decide +kernel
theorem PrimData50.q19 : PrimData50.s19.bok = true := by decide +kernel
theorem PrimData50.q20 : PrimData50.s20.bok = true := by decide +kernel
theorem PrimData50.q21 : PrimData50.s21.bok = true := by decide +kernel
theorem PrimData50.q22 : PrimData50.s22.bok = true := by decide +kernel
theorem PrimData50.q23 : PrimData50.s23.bok = true := by decide +kernel
theorem PrimData50.q24 : PrimData50.s24.bok = true := by decide +kernel
theorem PrimData50.q25 : PrimData50.s25.bok = true := by decide +kernel
theorem PrimData50.q26 : PrimData50.s26.bok = true := by decide +kernel
theorem PrimData50.q27 : PrimData50.s27.bok = true := by decide +kernel
theorem PrimData50.q28 : PrimData50.s28.bok = true := by decide +kernel
theorem PrimData50.q29 : PrimData50.s29.bok = true := by decide +kernel
theorem PrimData50.q30 : PrimData50.s30.bok = true := by decide +kernel
theorem PrimData50.q31 : PrimData50.s31.bok = true := by decide +kernel
theorem PrimData50.q32 : PrimData50.s32.bok = true := by decide +kernel
theorem PrimData50.q33 : PrimData50.s33.bok = true := by decide +kernel
theorem PrimData50.q34 : PrimData50.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData50.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData50.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData50.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData50.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData50.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
