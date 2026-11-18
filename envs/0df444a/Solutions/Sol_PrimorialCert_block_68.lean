-- Prove2me | solution 1 for PrimorialCert.block_68
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:07.173284+00:00
-- url     : https://prove2.me/submissions/27c366cf-c08a-4618-a077-b8ea9196f098

import Definitions.Def_PrimorialCertData_68

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData68.q0 : PrimData68.s0.bok = true := by decide +kernel
theorem PrimData68.q1 : PrimData68.s1.bok = true := by decide +kernel
theorem PrimData68.q2 : PrimData68.s2.bok = true := by decide +kernel
theorem PrimData68.q3 : PrimData68.s3.bok = true := by decide +kernel
theorem PrimData68.q4 : PrimData68.s4.bok = true := by decide +kernel
theorem PrimData68.q5 : PrimData68.s5.bok = true := by decide +kernel
theorem PrimData68.q6 : PrimData68.s6.bok = true := by decide +kernel
theorem PrimData68.q7 : PrimData68.s7.bok = true := by decide +kernel
theorem PrimData68.q8 : PrimData68.s8.bok = true := by decide +kernel
theorem PrimData68.q9 : PrimData68.s9.bok = true := by decide +kernel
theorem PrimData68.q10 : PrimData68.s10.bok = true := by decide +kernel
theorem PrimData68.q11 : PrimData68.s11.bok = true := by decide +kernel
theorem PrimData68.q12 : PrimData68.s12.bok = true := by decide +kernel
theorem PrimData68.q13 : PrimData68.s13.bok = true := by decide +kernel
theorem PrimData68.q14 : PrimData68.s14.bok = true := by decide +kernel
theorem PrimData68.q15 : PrimData68.s15.bok = true := by decide +kernel
theorem PrimData68.q16 : PrimData68.s16.bok = true := by decide +kernel
theorem PrimData68.q17 : PrimData68.s17.bok = true := by decide +kernel
theorem PrimData68.q18 : PrimData68.s18.bok = true := by decide +kernel
theorem PrimData68.q19 : PrimData68.s19.bok = true := by decide +kernel
theorem PrimData68.q20 : PrimData68.s20.bok = true := by decide +kernel
theorem PrimData68.q21 : PrimData68.s21.bok = true := by decide +kernel
theorem PrimData68.q22 : PrimData68.s22.bok = true := by decide +kernel
theorem PrimData68.q23 : PrimData68.s23.bok = true := by decide +kernel
theorem PrimData68.q24 : PrimData68.s24.bok = true := by decide +kernel
theorem PrimData68.q25 : PrimData68.s25.bok = true := by decide +kernel
theorem PrimData68.q26 : PrimData68.s26.bok = true := by decide +kernel
theorem PrimData68.q27 : PrimData68.s27.bok = true := by decide +kernel
theorem PrimData68.q28 : PrimData68.s28.bok = true := by decide +kernel
theorem PrimData68.q29 : PrimData68.s29.bok = true := by decide +kernel
theorem PrimData68.q30 : PrimData68.s30.bok = true := by decide +kernel
theorem PrimData68.q31 : PrimData68.s31.bok = true := by decide +kernel
theorem PrimData68.q32 : PrimData68.s32.bok = true := by decide +kernel
theorem PrimData68.q33 : PrimData68.s33.bok = true := by decide +kernel
theorem PrimData68.q34 : PrimData68.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData68.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData68.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData68.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData68.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData68.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
