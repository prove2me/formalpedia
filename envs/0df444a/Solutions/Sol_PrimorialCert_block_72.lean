-- Prove2me | solution 1 for PrimorialCert.block_72
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:15.287687+00:00
-- url     : https://prove2.me/submissions/dab03d56-5733-46b2-a0a9-7800d25ad46d

import Definitions.Def_PrimorialCertData_72

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData72.q0 : PrimData72.s0.bok = true := by decide +kernel
theorem PrimData72.q1 : PrimData72.s1.bok = true := by decide +kernel
theorem PrimData72.q2 : PrimData72.s2.bok = true := by decide +kernel
theorem PrimData72.q3 : PrimData72.s3.bok = true := by decide +kernel
theorem PrimData72.q4 : PrimData72.s4.bok = true := by decide +kernel
theorem PrimData72.q5 : PrimData72.s5.bok = true := by decide +kernel
theorem PrimData72.q6 : PrimData72.s6.bok = true := by decide +kernel
theorem PrimData72.q7 : PrimData72.s7.bok = true := by decide +kernel
theorem PrimData72.q8 : PrimData72.s8.bok = true := by decide +kernel
theorem PrimData72.q9 : PrimData72.s9.bok = true := by decide +kernel
theorem PrimData72.q10 : PrimData72.s10.bok = true := by decide +kernel
theorem PrimData72.q11 : PrimData72.s11.bok = true := by decide +kernel
theorem PrimData72.q12 : PrimData72.s12.bok = true := by decide +kernel
theorem PrimData72.q13 : PrimData72.s13.bok = true := by decide +kernel
theorem PrimData72.q14 : PrimData72.s14.bok = true := by decide +kernel
theorem PrimData72.q15 : PrimData72.s15.bok = true := by decide +kernel
theorem PrimData72.q16 : PrimData72.s16.bok = true := by decide +kernel
theorem PrimData72.q17 : PrimData72.s17.bok = true := by decide +kernel
theorem PrimData72.q18 : PrimData72.s18.bok = true := by decide +kernel
theorem PrimData72.q19 : PrimData72.s19.bok = true := by decide +kernel
theorem PrimData72.q20 : PrimData72.s20.bok = true := by decide +kernel
theorem PrimData72.q21 : PrimData72.s21.bok = true := by decide +kernel
theorem PrimData72.q22 : PrimData72.s22.bok = true := by decide +kernel
theorem PrimData72.q23 : PrimData72.s23.bok = true := by decide +kernel
theorem PrimData72.q24 : PrimData72.s24.bok = true := by decide +kernel
theorem PrimData72.q25 : PrimData72.s25.bok = true := by decide +kernel
theorem PrimData72.q26 : PrimData72.s26.bok = true := by decide +kernel
theorem PrimData72.q27 : PrimData72.s27.bok = true := by decide +kernel
theorem PrimData72.q28 : PrimData72.s28.bok = true := by decide +kernel
theorem PrimData72.q29 : PrimData72.s29.bok = true := by decide +kernel
theorem PrimData72.q30 : PrimData72.s30.bok = true := by decide +kernel
theorem PrimData72.q31 : PrimData72.s31.bok = true := by decide +kernel
theorem PrimData72.q32 : PrimData72.s32.bok = true := by decide +kernel
theorem PrimData72.q33 : PrimData72.s33.bok = true := by decide +kernel
theorem PrimData72.q34 : PrimData72.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData72.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData72.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData72.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData72.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData72.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
