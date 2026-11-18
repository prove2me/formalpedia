-- Prove2me | solution 1 for PrimorialCert.block_61
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:53.143007+00:00
-- url     : https://prove2.me/submissions/92142f1d-0b1c-4e8e-9a3d-ba394f8f33bb

import Definitions.Def_PrimorialCertData_61

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData61.q0 : PrimData61.s0.bok = true := by decide +kernel
theorem PrimData61.q1 : PrimData61.s1.bok = true := by decide +kernel
theorem PrimData61.q2 : PrimData61.s2.bok = true := by decide +kernel
theorem PrimData61.q3 : PrimData61.s3.bok = true := by decide +kernel
theorem PrimData61.q4 : PrimData61.s4.bok = true := by decide +kernel
theorem PrimData61.q5 : PrimData61.s5.bok = true := by decide +kernel
theorem PrimData61.q6 : PrimData61.s6.bok = true := by decide +kernel
theorem PrimData61.q7 : PrimData61.s7.bok = true := by decide +kernel
theorem PrimData61.q8 : PrimData61.s8.bok = true := by decide +kernel
theorem PrimData61.q9 : PrimData61.s9.bok = true := by decide +kernel
theorem PrimData61.q10 : PrimData61.s10.bok = true := by decide +kernel
theorem PrimData61.q11 : PrimData61.s11.bok = true := by decide +kernel
theorem PrimData61.q12 : PrimData61.s12.bok = true := by decide +kernel
theorem PrimData61.q13 : PrimData61.s13.bok = true := by decide +kernel
theorem PrimData61.q14 : PrimData61.s14.bok = true := by decide +kernel
theorem PrimData61.q15 : PrimData61.s15.bok = true := by decide +kernel
theorem PrimData61.q16 : PrimData61.s16.bok = true := by decide +kernel
theorem PrimData61.q17 : PrimData61.s17.bok = true := by decide +kernel
theorem PrimData61.q18 : PrimData61.s18.bok = true := by decide +kernel
theorem PrimData61.q19 : PrimData61.s19.bok = true := by decide +kernel
theorem PrimData61.q20 : PrimData61.s20.bok = true := by decide +kernel
theorem PrimData61.q21 : PrimData61.s21.bok = true := by decide +kernel
theorem PrimData61.q22 : PrimData61.s22.bok = true := by decide +kernel
theorem PrimData61.q23 : PrimData61.s23.bok = true := by decide +kernel
theorem PrimData61.q24 : PrimData61.s24.bok = true := by decide +kernel
theorem PrimData61.q25 : PrimData61.s25.bok = true := by decide +kernel
theorem PrimData61.q26 : PrimData61.s26.bok = true := by decide +kernel
theorem PrimData61.q27 : PrimData61.s27.bok = true := by decide +kernel
theorem PrimData61.q28 : PrimData61.s28.bok = true := by decide +kernel
theorem PrimData61.q29 : PrimData61.s29.bok = true := by decide +kernel
theorem PrimData61.q30 : PrimData61.s30.bok = true := by decide +kernel
theorem PrimData61.q31 : PrimData61.s31.bok = true := by decide +kernel
theorem PrimData61.q32 : PrimData61.s32.bok = true := by decide +kernel
theorem PrimData61.q33 : PrimData61.s33.bok = true := by decide +kernel
theorem PrimData61.q34 : PrimData61.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData61.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData61.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData61.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData61.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData61.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
