-- Prove2me | solution 1 for PrimorialCert.block_43
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:17.093994+00:00
-- url     : https://prove2.me/submissions/005e1b7e-914f-420d-8edf-130610652a6d

import Definitions.Def_PrimorialCertData_43

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData43.q0 : PrimData43.s0.bok = true := by decide +kernel
theorem PrimData43.q1 : PrimData43.s1.bok = true := by decide +kernel
theorem PrimData43.q2 : PrimData43.s2.bok = true := by decide +kernel
theorem PrimData43.q3 : PrimData43.s3.bok = true := by decide +kernel
theorem PrimData43.q4 : PrimData43.s4.bok = true := by decide +kernel
theorem PrimData43.q5 : PrimData43.s5.bok = true := by decide +kernel
theorem PrimData43.q6 : PrimData43.s6.bok = true := by decide +kernel
theorem PrimData43.q7 : PrimData43.s7.bok = true := by decide +kernel
theorem PrimData43.q8 : PrimData43.s8.bok = true := by decide +kernel
theorem PrimData43.q9 : PrimData43.s9.bok = true := by decide +kernel
theorem PrimData43.q10 : PrimData43.s10.bok = true := by decide +kernel
theorem PrimData43.q11 : PrimData43.s11.bok = true := by decide +kernel
theorem PrimData43.q12 : PrimData43.s12.bok = true := by decide +kernel
theorem PrimData43.q13 : PrimData43.s13.bok = true := by decide +kernel
theorem PrimData43.q14 : PrimData43.s14.bok = true := by decide +kernel
theorem PrimData43.q15 : PrimData43.s15.bok = true := by decide +kernel
theorem PrimData43.q16 : PrimData43.s16.bok = true := by decide +kernel
theorem PrimData43.q17 : PrimData43.s17.bok = true := by decide +kernel
theorem PrimData43.q18 : PrimData43.s18.bok = true := by decide +kernel
theorem PrimData43.q19 : PrimData43.s19.bok = true := by decide +kernel
theorem PrimData43.q20 : PrimData43.s20.bok = true := by decide +kernel
theorem PrimData43.q21 : PrimData43.s21.bok = true := by decide +kernel
theorem PrimData43.q22 : PrimData43.s22.bok = true := by decide +kernel
theorem PrimData43.q23 : PrimData43.s23.bok = true := by decide +kernel
theorem PrimData43.q24 : PrimData43.s24.bok = true := by decide +kernel
theorem PrimData43.q25 : PrimData43.s25.bok = true := by decide +kernel
theorem PrimData43.q26 : PrimData43.s26.bok = true := by decide +kernel
theorem PrimData43.q27 : PrimData43.s27.bok = true := by decide +kernel
theorem PrimData43.q28 : PrimData43.s28.bok = true := by decide +kernel
theorem PrimData43.q29 : PrimData43.s29.bok = true := by decide +kernel
theorem PrimData43.q30 : PrimData43.s30.bok = true := by decide +kernel
theorem PrimData43.q31 : PrimData43.s31.bok = true := by decide +kernel
theorem PrimData43.q32 : PrimData43.s32.bok = true := by decide +kernel
theorem PrimData43.q33 : PrimData43.s33.bok = true := by decide +kernel
theorem PrimData43.q34 : PrimData43.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData43.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData43.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData43.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData43.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData43.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
