-- Prove2me | solution 1 for PrimorialCert.block_46
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:23.10314+00:00
-- url     : https://prove2.me/submissions/c3386fec-a8e4-46b7-82c6-23c45e9dbc2c

import Definitions.Def_PrimorialCertData_46

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData46.q0 : PrimData46.s0.bok = true := by decide +kernel
theorem PrimData46.q1 : PrimData46.s1.bok = true := by decide +kernel
theorem PrimData46.q2 : PrimData46.s2.bok = true := by decide +kernel
theorem PrimData46.q3 : PrimData46.s3.bok = true := by decide +kernel
theorem PrimData46.q4 : PrimData46.s4.bok = true := by decide +kernel
theorem PrimData46.q5 : PrimData46.s5.bok = true := by decide +kernel
theorem PrimData46.q6 : PrimData46.s6.bok = true := by decide +kernel
theorem PrimData46.q7 : PrimData46.s7.bok = true := by decide +kernel
theorem PrimData46.q8 : PrimData46.s8.bok = true := by decide +kernel
theorem PrimData46.q9 : PrimData46.s9.bok = true := by decide +kernel
theorem PrimData46.q10 : PrimData46.s10.bok = true := by decide +kernel
theorem PrimData46.q11 : PrimData46.s11.bok = true := by decide +kernel
theorem PrimData46.q12 : PrimData46.s12.bok = true := by decide +kernel
theorem PrimData46.q13 : PrimData46.s13.bok = true := by decide +kernel
theorem PrimData46.q14 : PrimData46.s14.bok = true := by decide +kernel
theorem PrimData46.q15 : PrimData46.s15.bok = true := by decide +kernel
theorem PrimData46.q16 : PrimData46.s16.bok = true := by decide +kernel
theorem PrimData46.q17 : PrimData46.s17.bok = true := by decide +kernel
theorem PrimData46.q18 : PrimData46.s18.bok = true := by decide +kernel
theorem PrimData46.q19 : PrimData46.s19.bok = true := by decide +kernel
theorem PrimData46.q20 : PrimData46.s20.bok = true := by decide +kernel
theorem PrimData46.q21 : PrimData46.s21.bok = true := by decide +kernel
theorem PrimData46.q22 : PrimData46.s22.bok = true := by decide +kernel
theorem PrimData46.q23 : PrimData46.s23.bok = true := by decide +kernel
theorem PrimData46.q24 : PrimData46.s24.bok = true := by decide +kernel
theorem PrimData46.q25 : PrimData46.s25.bok = true := by decide +kernel
theorem PrimData46.q26 : PrimData46.s26.bok = true := by decide +kernel
theorem PrimData46.q27 : PrimData46.s27.bok = true := by decide +kernel
theorem PrimData46.q28 : PrimData46.s28.bok = true := by decide +kernel
theorem PrimData46.q29 : PrimData46.s29.bok = true := by decide +kernel
theorem PrimData46.q30 : PrimData46.s30.bok = true := by decide +kernel
theorem PrimData46.q31 : PrimData46.s31.bok = true := by decide +kernel
theorem PrimData46.q32 : PrimData46.s32.bok = true := by decide +kernel
theorem PrimData46.q33 : PrimData46.s33.bok = true := by decide +kernel
theorem PrimData46.q34 : PrimData46.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData46.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData46.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData46.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData46.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData46.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
