-- Prove2me | solution 1 for PrimorialCert.block_37
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:06.970031+00:00
-- url     : https://prove2.me/submissions/185fba34-f004-4f69-91a4-1ab97b062ec0

import Definitions.Def_PrimorialCertData_37

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData37.q0 : PrimData37.s0.bok = true := by decide +kernel
theorem PrimData37.q1 : PrimData37.s1.bok = true := by decide +kernel
theorem PrimData37.q2 : PrimData37.s2.bok = true := by decide +kernel
theorem PrimData37.q3 : PrimData37.s3.bok = true := by decide +kernel
theorem PrimData37.q4 : PrimData37.s4.bok = true := by decide +kernel
theorem PrimData37.q5 : PrimData37.s5.bok = true := by decide +kernel
theorem PrimData37.q6 : PrimData37.s6.bok = true := by decide +kernel
theorem PrimData37.q7 : PrimData37.s7.bok = true := by decide +kernel
theorem PrimData37.q8 : PrimData37.s8.bok = true := by decide +kernel
theorem PrimData37.q9 : PrimData37.s9.bok = true := by decide +kernel
theorem PrimData37.q10 : PrimData37.s10.bok = true := by decide +kernel
theorem PrimData37.q11 : PrimData37.s11.bok = true := by decide +kernel
theorem PrimData37.q12 : PrimData37.s12.bok = true := by decide +kernel
theorem PrimData37.q13 : PrimData37.s13.bok = true := by decide +kernel
theorem PrimData37.q14 : PrimData37.s14.bok = true := by decide +kernel
theorem PrimData37.q15 : PrimData37.s15.bok = true := by decide +kernel
theorem PrimData37.q16 : PrimData37.s16.bok = true := by decide +kernel
theorem PrimData37.q17 : PrimData37.s17.bok = true := by decide +kernel
theorem PrimData37.q18 : PrimData37.s18.bok = true := by decide +kernel
theorem PrimData37.q19 : PrimData37.s19.bok = true := by decide +kernel
theorem PrimData37.q20 : PrimData37.s20.bok = true := by decide +kernel
theorem PrimData37.q21 : PrimData37.s21.bok = true := by decide +kernel
theorem PrimData37.q22 : PrimData37.s22.bok = true := by decide +kernel
theorem PrimData37.q23 : PrimData37.s23.bok = true := by decide +kernel
theorem PrimData37.q24 : PrimData37.s24.bok = true := by decide +kernel
theorem PrimData37.q25 : PrimData37.s25.bok = true := by decide +kernel
theorem PrimData37.q26 : PrimData37.s26.bok = true := by decide +kernel
theorem PrimData37.q27 : PrimData37.s27.bok = true := by decide +kernel
theorem PrimData37.q28 : PrimData37.s28.bok = true := by decide +kernel
theorem PrimData37.q29 : PrimData37.s29.bok = true := by decide +kernel
theorem PrimData37.q30 : PrimData37.s30.bok = true := by decide +kernel
theorem PrimData37.q31 : PrimData37.s31.bok = true := by decide +kernel
theorem PrimData37.q32 : PrimData37.s32.bok = true := by decide +kernel
theorem PrimData37.q33 : PrimData37.s33.bok = true := by decide +kernel
theorem PrimData37.q34 : PrimData37.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData37.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData37.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData37.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData37.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData37.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
