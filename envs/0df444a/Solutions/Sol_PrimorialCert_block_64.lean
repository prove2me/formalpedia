-- Prove2me | solution 1 for PrimorialCert.block_64
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:59.171942+00:00
-- url     : https://prove2.me/submissions/a79b5d28-af32-41cc-ac6b-cb3f96242485

import Definitions.Def_PrimorialCertData_64

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData64.q0 : PrimData64.s0.bok = true := by decide +kernel
theorem PrimData64.q1 : PrimData64.s1.bok = true := by decide +kernel
theorem PrimData64.q2 : PrimData64.s2.bok = true := by decide +kernel
theorem PrimData64.q3 : PrimData64.s3.bok = true := by decide +kernel
theorem PrimData64.q4 : PrimData64.s4.bok = true := by decide +kernel
theorem PrimData64.q5 : PrimData64.s5.bok = true := by decide +kernel
theorem PrimData64.q6 : PrimData64.s6.bok = true := by decide +kernel
theorem PrimData64.q7 : PrimData64.s7.bok = true := by decide +kernel
theorem PrimData64.q8 : PrimData64.s8.bok = true := by decide +kernel
theorem PrimData64.q9 : PrimData64.s9.bok = true := by decide +kernel
theorem PrimData64.q10 : PrimData64.s10.bok = true := by decide +kernel
theorem PrimData64.q11 : PrimData64.s11.bok = true := by decide +kernel
theorem PrimData64.q12 : PrimData64.s12.bok = true := by decide +kernel
theorem PrimData64.q13 : PrimData64.s13.bok = true := by decide +kernel
theorem PrimData64.q14 : PrimData64.s14.bok = true := by decide +kernel
theorem PrimData64.q15 : PrimData64.s15.bok = true := by decide +kernel
theorem PrimData64.q16 : PrimData64.s16.bok = true := by decide +kernel
theorem PrimData64.q17 : PrimData64.s17.bok = true := by decide +kernel
theorem PrimData64.q18 : PrimData64.s18.bok = true := by decide +kernel
theorem PrimData64.q19 : PrimData64.s19.bok = true := by decide +kernel
theorem PrimData64.q20 : PrimData64.s20.bok = true := by decide +kernel
theorem PrimData64.q21 : PrimData64.s21.bok = true := by decide +kernel
theorem PrimData64.q22 : PrimData64.s22.bok = true := by decide +kernel
theorem PrimData64.q23 : PrimData64.s23.bok = true := by decide +kernel
theorem PrimData64.q24 : PrimData64.s24.bok = true := by decide +kernel
theorem PrimData64.q25 : PrimData64.s25.bok = true := by decide +kernel
theorem PrimData64.q26 : PrimData64.s26.bok = true := by decide +kernel
theorem PrimData64.q27 : PrimData64.s27.bok = true := by decide +kernel
theorem PrimData64.q28 : PrimData64.s28.bok = true := by decide +kernel
theorem PrimData64.q29 : PrimData64.s29.bok = true := by decide +kernel
theorem PrimData64.q30 : PrimData64.s30.bok = true := by decide +kernel
theorem PrimData64.q31 : PrimData64.s31.bok = true := by decide +kernel
theorem PrimData64.q32 : PrimData64.s32.bok = true := by decide +kernel
theorem PrimData64.q33 : PrimData64.s33.bok = true := by decide +kernel
theorem PrimData64.q34 : PrimData64.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData64.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData64.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData64.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData64.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData64.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
