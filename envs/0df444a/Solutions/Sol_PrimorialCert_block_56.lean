-- Prove2me | solution 1 for PrimorialCert.block_56
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:43.143967+00:00
-- url     : https://prove2.me/submissions/94714922-3241-4c18-9a4e-2d35abe319c8

import Definitions.Def_PrimorialCertData_56

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData56.q0 : PrimData56.s0.bok = true := by decide +kernel
theorem PrimData56.q1 : PrimData56.s1.bok = true := by decide +kernel
theorem PrimData56.q2 : PrimData56.s2.bok = true := by decide +kernel
theorem PrimData56.q3 : PrimData56.s3.bok = true := by decide +kernel
theorem PrimData56.q4 : PrimData56.s4.bok = true := by decide +kernel
theorem PrimData56.q5 : PrimData56.s5.bok = true := by decide +kernel
theorem PrimData56.q6 : PrimData56.s6.bok = true := by decide +kernel
theorem PrimData56.q7 : PrimData56.s7.bok = true := by decide +kernel
theorem PrimData56.q8 : PrimData56.s8.bok = true := by decide +kernel
theorem PrimData56.q9 : PrimData56.s9.bok = true := by decide +kernel
theorem PrimData56.q10 : PrimData56.s10.bok = true := by decide +kernel
theorem PrimData56.q11 : PrimData56.s11.bok = true := by decide +kernel
theorem PrimData56.q12 : PrimData56.s12.bok = true := by decide +kernel
theorem PrimData56.q13 : PrimData56.s13.bok = true := by decide +kernel
theorem PrimData56.q14 : PrimData56.s14.bok = true := by decide +kernel
theorem PrimData56.q15 : PrimData56.s15.bok = true := by decide +kernel
theorem PrimData56.q16 : PrimData56.s16.bok = true := by decide +kernel
theorem PrimData56.q17 : PrimData56.s17.bok = true := by decide +kernel
theorem PrimData56.q18 : PrimData56.s18.bok = true := by decide +kernel
theorem PrimData56.q19 : PrimData56.s19.bok = true := by decide +kernel
theorem PrimData56.q20 : PrimData56.s20.bok = true := by decide +kernel
theorem PrimData56.q21 : PrimData56.s21.bok = true := by decide +kernel
theorem PrimData56.q22 : PrimData56.s22.bok = true := by decide +kernel
theorem PrimData56.q23 : PrimData56.s23.bok = true := by decide +kernel
theorem PrimData56.q24 : PrimData56.s24.bok = true := by decide +kernel
theorem PrimData56.q25 : PrimData56.s25.bok = true := by decide +kernel
theorem PrimData56.q26 : PrimData56.s26.bok = true := by decide +kernel
theorem PrimData56.q27 : PrimData56.s27.bok = true := by decide +kernel
theorem PrimData56.q28 : PrimData56.s28.bok = true := by decide +kernel
theorem PrimData56.q29 : PrimData56.s29.bok = true := by decide +kernel
theorem PrimData56.q30 : PrimData56.s30.bok = true := by decide +kernel
theorem PrimData56.q31 : PrimData56.s31.bok = true := by decide +kernel
theorem PrimData56.q32 : PrimData56.s32.bok = true := by decide +kernel
theorem PrimData56.q33 : PrimData56.s33.bok = true := by decide +kernel
theorem PrimData56.q34 : PrimData56.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData56.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData56.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData56.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData56.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData56.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
