-- Prove2me | solution 1 for PrimorialCert.block_51
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:33.151219+00:00
-- url     : https://prove2.me/submissions/37ed47f3-986f-4c32-9383-5795c749a7e1

import Definitions.Def_PrimorialCertData_51

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData51.q0 : PrimData51.s0.bok = true := by decide +kernel
theorem PrimData51.q1 : PrimData51.s1.bok = true := by decide +kernel
theorem PrimData51.q2 : PrimData51.s2.bok = true := by decide +kernel
theorem PrimData51.q3 : PrimData51.s3.bok = true := by decide +kernel
theorem PrimData51.q4 : PrimData51.s4.bok = true := by decide +kernel
theorem PrimData51.q5 : PrimData51.s5.bok = true := by decide +kernel
theorem PrimData51.q6 : PrimData51.s6.bok = true := by decide +kernel
theorem PrimData51.q7 : PrimData51.s7.bok = true := by decide +kernel
theorem PrimData51.q8 : PrimData51.s8.bok = true := by decide +kernel
theorem PrimData51.q9 : PrimData51.s9.bok = true := by decide +kernel
theorem PrimData51.q10 : PrimData51.s10.bok = true := by decide +kernel
theorem PrimData51.q11 : PrimData51.s11.bok = true := by decide +kernel
theorem PrimData51.q12 : PrimData51.s12.bok = true := by decide +kernel
theorem PrimData51.q13 : PrimData51.s13.bok = true := by decide +kernel
theorem PrimData51.q14 : PrimData51.s14.bok = true := by decide +kernel
theorem PrimData51.q15 : PrimData51.s15.bok = true := by decide +kernel
theorem PrimData51.q16 : PrimData51.s16.bok = true := by decide +kernel
theorem PrimData51.q17 : PrimData51.s17.bok = true := by decide +kernel
theorem PrimData51.q18 : PrimData51.s18.bok = true := by decide +kernel
theorem PrimData51.q19 : PrimData51.s19.bok = true := by decide +kernel
theorem PrimData51.q20 : PrimData51.s20.bok = true := by decide +kernel
theorem PrimData51.q21 : PrimData51.s21.bok = true := by decide +kernel
theorem PrimData51.q22 : PrimData51.s22.bok = true := by decide +kernel
theorem PrimData51.q23 : PrimData51.s23.bok = true := by decide +kernel
theorem PrimData51.q24 : PrimData51.s24.bok = true := by decide +kernel
theorem PrimData51.q25 : PrimData51.s25.bok = true := by decide +kernel
theorem PrimData51.q26 : PrimData51.s26.bok = true := by decide +kernel
theorem PrimData51.q27 : PrimData51.s27.bok = true := by decide +kernel
theorem PrimData51.q28 : PrimData51.s28.bok = true := by decide +kernel
theorem PrimData51.q29 : PrimData51.s29.bok = true := by decide +kernel
theorem PrimData51.q30 : PrimData51.s30.bok = true := by decide +kernel
theorem PrimData51.q31 : PrimData51.s31.bok = true := by decide +kernel
theorem PrimData51.q32 : PrimData51.s32.bok = true := by decide +kernel
theorem PrimData51.q33 : PrimData51.s33.bok = true := by decide +kernel
theorem PrimData51.q34 : PrimData51.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData51.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData51.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData51.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData51.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData51.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
