-- Prove2me | solution 1 for PrimorialCert.block_44
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:19.046887+00:00
-- url     : https://prove2.me/submissions/afc12284-d849-4c8d-b579-857b6927478d

import Definitions.Def_PrimorialCertData_44

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData44.q0 : PrimData44.s0.bok = true := by decide +kernel
theorem PrimData44.q1 : PrimData44.s1.bok = true := by decide +kernel
theorem PrimData44.q2 : PrimData44.s2.bok = true := by decide +kernel
theorem PrimData44.q3 : PrimData44.s3.bok = true := by decide +kernel
theorem PrimData44.q4 : PrimData44.s4.bok = true := by decide +kernel
theorem PrimData44.q5 : PrimData44.s5.bok = true := by decide +kernel
theorem PrimData44.q6 : PrimData44.s6.bok = true := by decide +kernel
theorem PrimData44.q7 : PrimData44.s7.bok = true := by decide +kernel
theorem PrimData44.q8 : PrimData44.s8.bok = true := by decide +kernel
theorem PrimData44.q9 : PrimData44.s9.bok = true := by decide +kernel
theorem PrimData44.q10 : PrimData44.s10.bok = true := by decide +kernel
theorem PrimData44.q11 : PrimData44.s11.bok = true := by decide +kernel
theorem PrimData44.q12 : PrimData44.s12.bok = true := by decide +kernel
theorem PrimData44.q13 : PrimData44.s13.bok = true := by decide +kernel
theorem PrimData44.q14 : PrimData44.s14.bok = true := by decide +kernel
theorem PrimData44.q15 : PrimData44.s15.bok = true := by decide +kernel
theorem PrimData44.q16 : PrimData44.s16.bok = true := by decide +kernel
theorem PrimData44.q17 : PrimData44.s17.bok = true := by decide +kernel
theorem PrimData44.q18 : PrimData44.s18.bok = true := by decide +kernel
theorem PrimData44.q19 : PrimData44.s19.bok = true := by decide +kernel
theorem PrimData44.q20 : PrimData44.s20.bok = true := by decide +kernel
theorem PrimData44.q21 : PrimData44.s21.bok = true := by decide +kernel
theorem PrimData44.q22 : PrimData44.s22.bok = true := by decide +kernel
theorem PrimData44.q23 : PrimData44.s23.bok = true := by decide +kernel
theorem PrimData44.q24 : PrimData44.s24.bok = true := by decide +kernel
theorem PrimData44.q25 : PrimData44.s25.bok = true := by decide +kernel
theorem PrimData44.q26 : PrimData44.s26.bok = true := by decide +kernel
theorem PrimData44.q27 : PrimData44.s27.bok = true := by decide +kernel
theorem PrimData44.q28 : PrimData44.s28.bok = true := by decide +kernel
theorem PrimData44.q29 : PrimData44.s29.bok = true := by decide +kernel
theorem PrimData44.q30 : PrimData44.s30.bok = true := by decide +kernel
theorem PrimData44.q31 : PrimData44.s31.bok = true := by decide +kernel
theorem PrimData44.q32 : PrimData44.s32.bok = true := by decide +kernel
theorem PrimData44.q33 : PrimData44.s33.bok = true := by decide +kernel
theorem PrimData44.q34 : PrimData44.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData44.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData44.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData44.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData44.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData44.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
