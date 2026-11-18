-- Prove2me | solution 1 for PrimorialCert.block_73
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:17.243198+00:00
-- url     : https://prove2.me/submissions/d911ad63-1897-42b8-9c76-18595c72e6a7

import Definitions.Def_PrimorialCertData_73

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData73.q0 : PrimData73.s0.bok = true := by decide +kernel
theorem PrimData73.q1 : PrimData73.s1.bok = true := by decide +kernel
theorem PrimData73.q2 : PrimData73.s2.bok = true := by decide +kernel
theorem PrimData73.q3 : PrimData73.s3.bok = true := by decide +kernel
theorem PrimData73.q4 : PrimData73.s4.bok = true := by decide +kernel
theorem PrimData73.q5 : PrimData73.s5.bok = true := by decide +kernel
theorem PrimData73.q6 : PrimData73.s6.bok = true := by decide +kernel
theorem PrimData73.q7 : PrimData73.s7.bok = true := by decide +kernel
theorem PrimData73.q8 : PrimData73.s8.bok = true := by decide +kernel
theorem PrimData73.q9 : PrimData73.s9.bok = true := by decide +kernel
theorem PrimData73.q10 : PrimData73.s10.bok = true := by decide +kernel
theorem PrimData73.q11 : PrimData73.s11.bok = true := by decide +kernel
theorem PrimData73.q12 : PrimData73.s12.bok = true := by decide +kernel
theorem PrimData73.q13 : PrimData73.s13.bok = true := by decide +kernel
theorem PrimData73.q14 : PrimData73.s14.bok = true := by decide +kernel
theorem PrimData73.q15 : PrimData73.s15.bok = true := by decide +kernel
theorem PrimData73.q16 : PrimData73.s16.bok = true := by decide +kernel
theorem PrimData73.q17 : PrimData73.s17.bok = true := by decide +kernel
theorem PrimData73.q18 : PrimData73.s18.bok = true := by decide +kernel
theorem PrimData73.q19 : PrimData73.s19.bok = true := by decide +kernel
theorem PrimData73.q20 : PrimData73.s20.bok = true := by decide +kernel
theorem PrimData73.q21 : PrimData73.s21.bok = true := by decide +kernel
theorem PrimData73.q22 : PrimData73.s22.bok = true := by decide +kernel
theorem PrimData73.q23 : PrimData73.s23.bok = true := by decide +kernel
theorem PrimData73.q24 : PrimData73.s24.bok = true := by decide +kernel
theorem PrimData73.q25 : PrimData73.s25.bok = true := by decide +kernel
theorem PrimData73.q26 : PrimData73.s26.bok = true := by decide +kernel
theorem PrimData73.q27 : PrimData73.s27.bok = true := by decide +kernel
theorem PrimData73.q28 : PrimData73.s28.bok = true := by decide +kernel
theorem PrimData73.q29 : PrimData73.s29.bok = true := by decide +kernel
theorem PrimData73.q30 : PrimData73.s30.bok = true := by decide +kernel
theorem PrimData73.q31 : PrimData73.s31.bok = true := by decide +kernel
theorem PrimData73.q32 : PrimData73.s32.bok = true := by decide +kernel
theorem PrimData73.q33 : PrimData73.s33.bok = true := by decide +kernel
theorem PrimData73.q34 : PrimData73.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData73.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData73.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData73.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData73.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData73.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
