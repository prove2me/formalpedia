-- Prove2me | solution 1 for PrimorialCert.block_23
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:38.893019+00:00
-- url     : https://prove2.me/submissions/573429a1-b34e-4004-9296-a85883dc9040

import Definitions.Def_PrimorialCertData_23

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData23.q0 : PrimData23.s0.bok = true := by decide +kernel
theorem PrimData23.q1 : PrimData23.s1.bok = true := by decide +kernel
theorem PrimData23.q2 : PrimData23.s2.bok = true := by decide +kernel
theorem PrimData23.q3 : PrimData23.s3.bok = true := by decide +kernel
theorem PrimData23.q4 : PrimData23.s4.bok = true := by decide +kernel
theorem PrimData23.q5 : PrimData23.s5.bok = true := by decide +kernel
theorem PrimData23.q6 : PrimData23.s6.bok = true := by decide +kernel
theorem PrimData23.q7 : PrimData23.s7.bok = true := by decide +kernel
theorem PrimData23.q8 : PrimData23.s8.bok = true := by decide +kernel
theorem PrimData23.q9 : PrimData23.s9.bok = true := by decide +kernel
theorem PrimData23.q10 : PrimData23.s10.bok = true := by decide +kernel
theorem PrimData23.q11 : PrimData23.s11.bok = true := by decide +kernel
theorem PrimData23.q12 : PrimData23.s12.bok = true := by decide +kernel
theorem PrimData23.q13 : PrimData23.s13.bok = true := by decide +kernel
theorem PrimData23.q14 : PrimData23.s14.bok = true := by decide +kernel
theorem PrimData23.q15 : PrimData23.s15.bok = true := by decide +kernel
theorem PrimData23.q16 : PrimData23.s16.bok = true := by decide +kernel
theorem PrimData23.q17 : PrimData23.s17.bok = true := by decide +kernel
theorem PrimData23.q18 : PrimData23.s18.bok = true := by decide +kernel
theorem PrimData23.q19 : PrimData23.s19.bok = true := by decide +kernel
theorem PrimData23.q20 : PrimData23.s20.bok = true := by decide +kernel
theorem PrimData23.q21 : PrimData23.s21.bok = true := by decide +kernel
theorem PrimData23.q22 : PrimData23.s22.bok = true := by decide +kernel
theorem PrimData23.q23 : PrimData23.s23.bok = true := by decide +kernel
theorem PrimData23.q24 : PrimData23.s24.bok = true := by decide +kernel
theorem PrimData23.q25 : PrimData23.s25.bok = true := by decide +kernel
theorem PrimData23.q26 : PrimData23.s26.bok = true := by decide +kernel
theorem PrimData23.q27 : PrimData23.s27.bok = true := by decide +kernel
theorem PrimData23.q28 : PrimData23.s28.bok = true := by decide +kernel
theorem PrimData23.q29 : PrimData23.s29.bok = true := by decide +kernel
theorem PrimData23.q30 : PrimData23.s30.bok = true := by decide +kernel
theorem PrimData23.q31 : PrimData23.s31.bok = true := by decide +kernel
theorem PrimData23.q32 : PrimData23.s32.bok = true := by decide +kernel
theorem PrimData23.q33 : PrimData23.s33.bok = true := by decide +kernel
theorem PrimData23.q34 : PrimData23.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData23.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData23.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData23.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData23.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData23.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
