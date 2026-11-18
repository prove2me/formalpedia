-- Prove2me | solution 1 for PrimorialCert.block_53
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:37.065506+00:00
-- url     : https://prove2.me/submissions/82315273-8687-499d-b442-dfba527f1414

import Definitions.Def_PrimorialCertData_53

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData53.q0 : PrimData53.s0.bok = true := by decide +kernel
theorem PrimData53.q1 : PrimData53.s1.bok = true := by decide +kernel
theorem PrimData53.q2 : PrimData53.s2.bok = true := by decide +kernel
theorem PrimData53.q3 : PrimData53.s3.bok = true := by decide +kernel
theorem PrimData53.q4 : PrimData53.s4.bok = true := by decide +kernel
theorem PrimData53.q5 : PrimData53.s5.bok = true := by decide +kernel
theorem PrimData53.q6 : PrimData53.s6.bok = true := by decide +kernel
theorem PrimData53.q7 : PrimData53.s7.bok = true := by decide +kernel
theorem PrimData53.q8 : PrimData53.s8.bok = true := by decide +kernel
theorem PrimData53.q9 : PrimData53.s9.bok = true := by decide +kernel
theorem PrimData53.q10 : PrimData53.s10.bok = true := by decide +kernel
theorem PrimData53.q11 : PrimData53.s11.bok = true := by decide +kernel
theorem PrimData53.q12 : PrimData53.s12.bok = true := by decide +kernel
theorem PrimData53.q13 : PrimData53.s13.bok = true := by decide +kernel
theorem PrimData53.q14 : PrimData53.s14.bok = true := by decide +kernel
theorem PrimData53.q15 : PrimData53.s15.bok = true := by decide +kernel
theorem PrimData53.q16 : PrimData53.s16.bok = true := by decide +kernel
theorem PrimData53.q17 : PrimData53.s17.bok = true := by decide +kernel
theorem PrimData53.q18 : PrimData53.s18.bok = true := by decide +kernel
theorem PrimData53.q19 : PrimData53.s19.bok = true := by decide +kernel
theorem PrimData53.q20 : PrimData53.s20.bok = true := by decide +kernel
theorem PrimData53.q21 : PrimData53.s21.bok = true := by decide +kernel
theorem PrimData53.q22 : PrimData53.s22.bok = true := by decide +kernel
theorem PrimData53.q23 : PrimData53.s23.bok = true := by decide +kernel
theorem PrimData53.q24 : PrimData53.s24.bok = true := by decide +kernel
theorem PrimData53.q25 : PrimData53.s25.bok = true := by decide +kernel
theorem PrimData53.q26 : PrimData53.s26.bok = true := by decide +kernel
theorem PrimData53.q27 : PrimData53.s27.bok = true := by decide +kernel
theorem PrimData53.q28 : PrimData53.s28.bok = true := by decide +kernel
theorem PrimData53.q29 : PrimData53.s29.bok = true := by decide +kernel
theorem PrimData53.q30 : PrimData53.s30.bok = true := by decide +kernel
theorem PrimData53.q31 : PrimData53.s31.bok = true := by decide +kernel
theorem PrimData53.q32 : PrimData53.s32.bok = true := by decide +kernel
theorem PrimData53.q33 : PrimData53.s33.bok = true := by decide +kernel
theorem PrimData53.q34 : PrimData53.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData53.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData53.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData53.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData53.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData53.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
