-- Prove2me | solution 1 for PrimorialCert.block_57
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:45.105833+00:00
-- url     : https://prove2.me/submissions/fee5976b-1d65-4381-8a33-00420fd2a30d

import Definitions.Def_PrimorialCertData_57

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData57.q0 : PrimData57.s0.bok = true := by decide +kernel
theorem PrimData57.q1 : PrimData57.s1.bok = true := by decide +kernel
theorem PrimData57.q2 : PrimData57.s2.bok = true := by decide +kernel
theorem PrimData57.q3 : PrimData57.s3.bok = true := by decide +kernel
theorem PrimData57.q4 : PrimData57.s4.bok = true := by decide +kernel
theorem PrimData57.q5 : PrimData57.s5.bok = true := by decide +kernel
theorem PrimData57.q6 : PrimData57.s6.bok = true := by decide +kernel
theorem PrimData57.q7 : PrimData57.s7.bok = true := by decide +kernel
theorem PrimData57.q8 : PrimData57.s8.bok = true := by decide +kernel
theorem PrimData57.q9 : PrimData57.s9.bok = true := by decide +kernel
theorem PrimData57.q10 : PrimData57.s10.bok = true := by decide +kernel
theorem PrimData57.q11 : PrimData57.s11.bok = true := by decide +kernel
theorem PrimData57.q12 : PrimData57.s12.bok = true := by decide +kernel
theorem PrimData57.q13 : PrimData57.s13.bok = true := by decide +kernel
theorem PrimData57.q14 : PrimData57.s14.bok = true := by decide +kernel
theorem PrimData57.q15 : PrimData57.s15.bok = true := by decide +kernel
theorem PrimData57.q16 : PrimData57.s16.bok = true := by decide +kernel
theorem PrimData57.q17 : PrimData57.s17.bok = true := by decide +kernel
theorem PrimData57.q18 : PrimData57.s18.bok = true := by decide +kernel
theorem PrimData57.q19 : PrimData57.s19.bok = true := by decide +kernel
theorem PrimData57.q20 : PrimData57.s20.bok = true := by decide +kernel
theorem PrimData57.q21 : PrimData57.s21.bok = true := by decide +kernel
theorem PrimData57.q22 : PrimData57.s22.bok = true := by decide +kernel
theorem PrimData57.q23 : PrimData57.s23.bok = true := by decide +kernel
theorem PrimData57.q24 : PrimData57.s24.bok = true := by decide +kernel
theorem PrimData57.q25 : PrimData57.s25.bok = true := by decide +kernel
theorem PrimData57.q26 : PrimData57.s26.bok = true := by decide +kernel
theorem PrimData57.q27 : PrimData57.s27.bok = true := by decide +kernel
theorem PrimData57.q28 : PrimData57.s28.bok = true := by decide +kernel
theorem PrimData57.q29 : PrimData57.s29.bok = true := by decide +kernel
theorem PrimData57.q30 : PrimData57.s30.bok = true := by decide +kernel
theorem PrimData57.q31 : PrimData57.s31.bok = true := by decide +kernel
theorem PrimData57.q32 : PrimData57.s32.bok = true := by decide +kernel
theorem PrimData57.q33 : PrimData57.s33.bok = true := by decide +kernel
theorem PrimData57.q34 : PrimData57.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData57.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData57.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData57.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData57.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData57.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
