-- Prove2me | solution 1 for PrimorialCert.block_22
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:36.932201+00:00
-- url     : https://prove2.me/submissions/2d346b79-e48a-494a-bb44-bc52ae062c96

import Definitions.Def_PrimorialCertData_22

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData22.q0 : PrimData22.s0.bok = true := by decide +kernel
theorem PrimData22.q1 : PrimData22.s1.bok = true := by decide +kernel
theorem PrimData22.q2 : PrimData22.s2.bok = true := by decide +kernel
theorem PrimData22.q3 : PrimData22.s3.bok = true := by decide +kernel
theorem PrimData22.q4 : PrimData22.s4.bok = true := by decide +kernel
theorem PrimData22.q5 : PrimData22.s5.bok = true := by decide +kernel
theorem PrimData22.q6 : PrimData22.s6.bok = true := by decide +kernel
theorem PrimData22.q7 : PrimData22.s7.bok = true := by decide +kernel
theorem PrimData22.q8 : PrimData22.s8.bok = true := by decide +kernel
theorem PrimData22.q9 : PrimData22.s9.bok = true := by decide +kernel
theorem PrimData22.q10 : PrimData22.s10.bok = true := by decide +kernel
theorem PrimData22.q11 : PrimData22.s11.bok = true := by decide +kernel
theorem PrimData22.q12 : PrimData22.s12.bok = true := by decide +kernel
theorem PrimData22.q13 : PrimData22.s13.bok = true := by decide +kernel
theorem PrimData22.q14 : PrimData22.s14.bok = true := by decide +kernel
theorem PrimData22.q15 : PrimData22.s15.bok = true := by decide +kernel
theorem PrimData22.q16 : PrimData22.s16.bok = true := by decide +kernel
theorem PrimData22.q17 : PrimData22.s17.bok = true := by decide +kernel
theorem PrimData22.q18 : PrimData22.s18.bok = true := by decide +kernel
theorem PrimData22.q19 : PrimData22.s19.bok = true := by decide +kernel
theorem PrimData22.q20 : PrimData22.s20.bok = true := by decide +kernel
theorem PrimData22.q21 : PrimData22.s21.bok = true := by decide +kernel
theorem PrimData22.q22 : PrimData22.s22.bok = true := by decide +kernel
theorem PrimData22.q23 : PrimData22.s23.bok = true := by decide +kernel
theorem PrimData22.q24 : PrimData22.s24.bok = true := by decide +kernel
theorem PrimData22.q25 : PrimData22.s25.bok = true := by decide +kernel
theorem PrimData22.q26 : PrimData22.s26.bok = true := by decide +kernel
theorem PrimData22.q27 : PrimData22.s27.bok = true := by decide +kernel
theorem PrimData22.q28 : PrimData22.s28.bok = true := by decide +kernel
theorem PrimData22.q29 : PrimData22.s29.bok = true := by decide +kernel
theorem PrimData22.q30 : PrimData22.s30.bok = true := by decide +kernel
theorem PrimData22.q31 : PrimData22.s31.bok = true := by decide +kernel
theorem PrimData22.q32 : PrimData22.s32.bok = true := by decide +kernel
theorem PrimData22.q33 : PrimData22.s33.bok = true := by decide +kernel
theorem PrimData22.q34 : PrimData22.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData22.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData22.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData22.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData22.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData22.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
