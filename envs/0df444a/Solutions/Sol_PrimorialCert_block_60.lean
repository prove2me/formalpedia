-- Prove2me | solution 1 for PrimorialCert.block_60
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:51.077542+00:00
-- url     : https://prove2.me/submissions/80de8182-aa2a-4e13-8c92-76d068e16bbe

import Definitions.Def_PrimorialCertData_60

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData60.q0 : PrimData60.s0.bok = true := by decide +kernel
theorem PrimData60.q1 : PrimData60.s1.bok = true := by decide +kernel
theorem PrimData60.q2 : PrimData60.s2.bok = true := by decide +kernel
theorem PrimData60.q3 : PrimData60.s3.bok = true := by decide +kernel
theorem PrimData60.q4 : PrimData60.s4.bok = true := by decide +kernel
theorem PrimData60.q5 : PrimData60.s5.bok = true := by decide +kernel
theorem PrimData60.q6 : PrimData60.s6.bok = true := by decide +kernel
theorem PrimData60.q7 : PrimData60.s7.bok = true := by decide +kernel
theorem PrimData60.q8 : PrimData60.s8.bok = true := by decide +kernel
theorem PrimData60.q9 : PrimData60.s9.bok = true := by decide +kernel
theorem PrimData60.q10 : PrimData60.s10.bok = true := by decide +kernel
theorem PrimData60.q11 : PrimData60.s11.bok = true := by decide +kernel
theorem PrimData60.q12 : PrimData60.s12.bok = true := by decide +kernel
theorem PrimData60.q13 : PrimData60.s13.bok = true := by decide +kernel
theorem PrimData60.q14 : PrimData60.s14.bok = true := by decide +kernel
theorem PrimData60.q15 : PrimData60.s15.bok = true := by decide +kernel
theorem PrimData60.q16 : PrimData60.s16.bok = true := by decide +kernel
theorem PrimData60.q17 : PrimData60.s17.bok = true := by decide +kernel
theorem PrimData60.q18 : PrimData60.s18.bok = true := by decide +kernel
theorem PrimData60.q19 : PrimData60.s19.bok = true := by decide +kernel
theorem PrimData60.q20 : PrimData60.s20.bok = true := by decide +kernel
theorem PrimData60.q21 : PrimData60.s21.bok = true := by decide +kernel
theorem PrimData60.q22 : PrimData60.s22.bok = true := by decide +kernel
theorem PrimData60.q23 : PrimData60.s23.bok = true := by decide +kernel
theorem PrimData60.q24 : PrimData60.s24.bok = true := by decide +kernel
theorem PrimData60.q25 : PrimData60.s25.bok = true := by decide +kernel
theorem PrimData60.q26 : PrimData60.s26.bok = true := by decide +kernel
theorem PrimData60.q27 : PrimData60.s27.bok = true := by decide +kernel
theorem PrimData60.q28 : PrimData60.s28.bok = true := by decide +kernel
theorem PrimData60.q29 : PrimData60.s29.bok = true := by decide +kernel
theorem PrimData60.q30 : PrimData60.s30.bok = true := by decide +kernel
theorem PrimData60.q31 : PrimData60.s31.bok = true := by decide +kernel
theorem PrimData60.q32 : PrimData60.s32.bok = true := by decide +kernel
theorem PrimData60.q33 : PrimData60.s33.bok = true := by decide +kernel
theorem PrimData60.q34 : PrimData60.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData60.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData60.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData60.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData60.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData60.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
