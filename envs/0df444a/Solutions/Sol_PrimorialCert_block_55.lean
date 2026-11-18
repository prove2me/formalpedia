-- Prove2me | solution 1 for PrimorialCert.block_55
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:41.069083+00:00
-- url     : https://prove2.me/submissions/50ff4a5e-15ea-4adc-b070-d2c6429ff261

import Definitions.Def_PrimorialCertData_55

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData55.q0 : PrimData55.s0.bok = true := by decide +kernel
theorem PrimData55.q1 : PrimData55.s1.bok = true := by decide +kernel
theorem PrimData55.q2 : PrimData55.s2.bok = true := by decide +kernel
theorem PrimData55.q3 : PrimData55.s3.bok = true := by decide +kernel
theorem PrimData55.q4 : PrimData55.s4.bok = true := by decide +kernel
theorem PrimData55.q5 : PrimData55.s5.bok = true := by decide +kernel
theorem PrimData55.q6 : PrimData55.s6.bok = true := by decide +kernel
theorem PrimData55.q7 : PrimData55.s7.bok = true := by decide +kernel
theorem PrimData55.q8 : PrimData55.s8.bok = true := by decide +kernel
theorem PrimData55.q9 : PrimData55.s9.bok = true := by decide +kernel
theorem PrimData55.q10 : PrimData55.s10.bok = true := by decide +kernel
theorem PrimData55.q11 : PrimData55.s11.bok = true := by decide +kernel
theorem PrimData55.q12 : PrimData55.s12.bok = true := by decide +kernel
theorem PrimData55.q13 : PrimData55.s13.bok = true := by decide +kernel
theorem PrimData55.q14 : PrimData55.s14.bok = true := by decide +kernel
theorem PrimData55.q15 : PrimData55.s15.bok = true := by decide +kernel
theorem PrimData55.q16 : PrimData55.s16.bok = true := by decide +kernel
theorem PrimData55.q17 : PrimData55.s17.bok = true := by decide +kernel
theorem PrimData55.q18 : PrimData55.s18.bok = true := by decide +kernel
theorem PrimData55.q19 : PrimData55.s19.bok = true := by decide +kernel
theorem PrimData55.q20 : PrimData55.s20.bok = true := by decide +kernel
theorem PrimData55.q21 : PrimData55.s21.bok = true := by decide +kernel
theorem PrimData55.q22 : PrimData55.s22.bok = true := by decide +kernel
theorem PrimData55.q23 : PrimData55.s23.bok = true := by decide +kernel
theorem PrimData55.q24 : PrimData55.s24.bok = true := by decide +kernel
theorem PrimData55.q25 : PrimData55.s25.bok = true := by decide +kernel
theorem PrimData55.q26 : PrimData55.s26.bok = true := by decide +kernel
theorem PrimData55.q27 : PrimData55.s27.bok = true := by decide +kernel
theorem PrimData55.q28 : PrimData55.s28.bok = true := by decide +kernel
theorem PrimData55.q29 : PrimData55.s29.bok = true := by decide +kernel
theorem PrimData55.q30 : PrimData55.s30.bok = true := by decide +kernel
theorem PrimData55.q31 : PrimData55.s31.bok = true := by decide +kernel
theorem PrimData55.q32 : PrimData55.s32.bok = true := by decide +kernel
theorem PrimData55.q33 : PrimData55.s33.bok = true := by decide +kernel
theorem PrimData55.q34 : PrimData55.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData55.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData55.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData55.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData55.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData55.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
