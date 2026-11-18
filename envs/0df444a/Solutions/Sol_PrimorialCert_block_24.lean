-- Prove2me | solution 1 for PrimorialCert.block_24
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:40.87176+00:00
-- url     : https://prove2.me/submissions/4db43a40-d930-4756-869a-9df4b93f5503

import Definitions.Def_PrimorialCertData_24

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData24.q0 : PrimData24.s0.bok = true := by decide +kernel
theorem PrimData24.q1 : PrimData24.s1.bok = true := by decide +kernel
theorem PrimData24.q2 : PrimData24.s2.bok = true := by decide +kernel
theorem PrimData24.q3 : PrimData24.s3.bok = true := by decide +kernel
theorem PrimData24.q4 : PrimData24.s4.bok = true := by decide +kernel
theorem PrimData24.q5 : PrimData24.s5.bok = true := by decide +kernel
theorem PrimData24.q6 : PrimData24.s6.bok = true := by decide +kernel
theorem PrimData24.q7 : PrimData24.s7.bok = true := by decide +kernel
theorem PrimData24.q8 : PrimData24.s8.bok = true := by decide +kernel
theorem PrimData24.q9 : PrimData24.s9.bok = true := by decide +kernel
theorem PrimData24.q10 : PrimData24.s10.bok = true := by decide +kernel
theorem PrimData24.q11 : PrimData24.s11.bok = true := by decide +kernel
theorem PrimData24.q12 : PrimData24.s12.bok = true := by decide +kernel
theorem PrimData24.q13 : PrimData24.s13.bok = true := by decide +kernel
theorem PrimData24.q14 : PrimData24.s14.bok = true := by decide +kernel
theorem PrimData24.q15 : PrimData24.s15.bok = true := by decide +kernel
theorem PrimData24.q16 : PrimData24.s16.bok = true := by decide +kernel
theorem PrimData24.q17 : PrimData24.s17.bok = true := by decide +kernel
theorem PrimData24.q18 : PrimData24.s18.bok = true := by decide +kernel
theorem PrimData24.q19 : PrimData24.s19.bok = true := by decide +kernel
theorem PrimData24.q20 : PrimData24.s20.bok = true := by decide +kernel
theorem PrimData24.q21 : PrimData24.s21.bok = true := by decide +kernel
theorem PrimData24.q22 : PrimData24.s22.bok = true := by decide +kernel
theorem PrimData24.q23 : PrimData24.s23.bok = true := by decide +kernel
theorem PrimData24.q24 : PrimData24.s24.bok = true := by decide +kernel
theorem PrimData24.q25 : PrimData24.s25.bok = true := by decide +kernel
theorem PrimData24.q26 : PrimData24.s26.bok = true := by decide +kernel
theorem PrimData24.q27 : PrimData24.s27.bok = true := by decide +kernel
theorem PrimData24.q28 : PrimData24.s28.bok = true := by decide +kernel
theorem PrimData24.q29 : PrimData24.s29.bok = true := by decide +kernel
theorem PrimData24.q30 : PrimData24.s30.bok = true := by decide +kernel
theorem PrimData24.q31 : PrimData24.s31.bok = true := by decide +kernel
theorem PrimData24.q32 : PrimData24.s32.bok = true := by decide +kernel
theorem PrimData24.q33 : PrimData24.s33.bok = true := by decide +kernel
theorem PrimData24.q34 : PrimData24.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData24.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData24.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData24.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData24.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData24.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
