-- Prove2me | solution 1 for PrimorialCert.block_59
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:49.071381+00:00
-- url     : https://prove2.me/submissions/9d5c65e0-39ac-4e85-9f9e-492656ff9c78

import Definitions.Def_PrimorialCertData_59

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData59.q0 : PrimData59.s0.bok = true := by decide +kernel
theorem PrimData59.q1 : PrimData59.s1.bok = true := by decide +kernel
theorem PrimData59.q2 : PrimData59.s2.bok = true := by decide +kernel
theorem PrimData59.q3 : PrimData59.s3.bok = true := by decide +kernel
theorem PrimData59.q4 : PrimData59.s4.bok = true := by decide +kernel
theorem PrimData59.q5 : PrimData59.s5.bok = true := by decide +kernel
theorem PrimData59.q6 : PrimData59.s6.bok = true := by decide +kernel
theorem PrimData59.q7 : PrimData59.s7.bok = true := by decide +kernel
theorem PrimData59.q8 : PrimData59.s8.bok = true := by decide +kernel
theorem PrimData59.q9 : PrimData59.s9.bok = true := by decide +kernel
theorem PrimData59.q10 : PrimData59.s10.bok = true := by decide +kernel
theorem PrimData59.q11 : PrimData59.s11.bok = true := by decide +kernel
theorem PrimData59.q12 : PrimData59.s12.bok = true := by decide +kernel
theorem PrimData59.q13 : PrimData59.s13.bok = true := by decide +kernel
theorem PrimData59.q14 : PrimData59.s14.bok = true := by decide +kernel
theorem PrimData59.q15 : PrimData59.s15.bok = true := by decide +kernel
theorem PrimData59.q16 : PrimData59.s16.bok = true := by decide +kernel
theorem PrimData59.q17 : PrimData59.s17.bok = true := by decide +kernel
theorem PrimData59.q18 : PrimData59.s18.bok = true := by decide +kernel
theorem PrimData59.q19 : PrimData59.s19.bok = true := by decide +kernel
theorem PrimData59.q20 : PrimData59.s20.bok = true := by decide +kernel
theorem PrimData59.q21 : PrimData59.s21.bok = true := by decide +kernel
theorem PrimData59.q22 : PrimData59.s22.bok = true := by decide +kernel
theorem PrimData59.q23 : PrimData59.s23.bok = true := by decide +kernel
theorem PrimData59.q24 : PrimData59.s24.bok = true := by decide +kernel
theorem PrimData59.q25 : PrimData59.s25.bok = true := by decide +kernel
theorem PrimData59.q26 : PrimData59.s26.bok = true := by decide +kernel
theorem PrimData59.q27 : PrimData59.s27.bok = true := by decide +kernel
theorem PrimData59.q28 : PrimData59.s28.bok = true := by decide +kernel
theorem PrimData59.q29 : PrimData59.s29.bok = true := by decide +kernel
theorem PrimData59.q30 : PrimData59.s30.bok = true := by decide +kernel
theorem PrimData59.q31 : PrimData59.s31.bok = true := by decide +kernel
theorem PrimData59.q32 : PrimData59.s32.bok = true := by decide +kernel
theorem PrimData59.q33 : PrimData59.s33.bok = true := by decide +kernel
theorem PrimData59.q34 : PrimData59.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData59.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData59.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData59.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData59.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData59.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
