-- Prove2me | solution 1 for PrimorialCert.block_19
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:30.832578+00:00
-- url     : https://prove2.me/submissions/f143d83b-95a6-437b-bf88-3943f4549b13

import Definitions.Def_PrimorialCertData_19

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData19.q0 : PrimData19.s0.bok = true := by decide +kernel
theorem PrimData19.q1 : PrimData19.s1.bok = true := by decide +kernel
theorem PrimData19.q2 : PrimData19.s2.bok = true := by decide +kernel
theorem PrimData19.q3 : PrimData19.s3.bok = true := by decide +kernel
theorem PrimData19.q4 : PrimData19.s4.bok = true := by decide +kernel
theorem PrimData19.q5 : PrimData19.s5.bok = true := by decide +kernel
theorem PrimData19.q6 : PrimData19.s6.bok = true := by decide +kernel
theorem PrimData19.q7 : PrimData19.s7.bok = true := by decide +kernel
theorem PrimData19.q8 : PrimData19.s8.bok = true := by decide +kernel
theorem PrimData19.q9 : PrimData19.s9.bok = true := by decide +kernel
theorem PrimData19.q10 : PrimData19.s10.bok = true := by decide +kernel
theorem PrimData19.q11 : PrimData19.s11.bok = true := by decide +kernel
theorem PrimData19.q12 : PrimData19.s12.bok = true := by decide +kernel
theorem PrimData19.q13 : PrimData19.s13.bok = true := by decide +kernel
theorem PrimData19.q14 : PrimData19.s14.bok = true := by decide +kernel
theorem PrimData19.q15 : PrimData19.s15.bok = true := by decide +kernel
theorem PrimData19.q16 : PrimData19.s16.bok = true := by decide +kernel
theorem PrimData19.q17 : PrimData19.s17.bok = true := by decide +kernel
theorem PrimData19.q18 : PrimData19.s18.bok = true := by decide +kernel
theorem PrimData19.q19 : PrimData19.s19.bok = true := by decide +kernel
theorem PrimData19.q20 : PrimData19.s20.bok = true := by decide +kernel
theorem PrimData19.q21 : PrimData19.s21.bok = true := by decide +kernel
theorem PrimData19.q22 : PrimData19.s22.bok = true := by decide +kernel
theorem PrimData19.q23 : PrimData19.s23.bok = true := by decide +kernel
theorem PrimData19.q24 : PrimData19.s24.bok = true := by decide +kernel
theorem PrimData19.q25 : PrimData19.s25.bok = true := by decide +kernel
theorem PrimData19.q26 : PrimData19.s26.bok = true := by decide +kernel
theorem PrimData19.q27 : PrimData19.s27.bok = true := by decide +kernel
theorem PrimData19.q28 : PrimData19.s28.bok = true := by decide +kernel
theorem PrimData19.q29 : PrimData19.s29.bok = true := by decide +kernel
theorem PrimData19.q30 : PrimData19.s30.bok = true := by decide +kernel
theorem PrimData19.q31 : PrimData19.s31.bok = true := by decide +kernel
theorem PrimData19.q32 : PrimData19.s32.bok = true := by decide +kernel
theorem PrimData19.q33 : PrimData19.s33.bok = true := by decide +kernel
theorem PrimData19.q34 : PrimData19.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData19.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData19.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData19.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData19.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData19.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
