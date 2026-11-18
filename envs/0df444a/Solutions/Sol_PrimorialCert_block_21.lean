-- Prove2me | solution 1 for PrimorialCert.block_21
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:34.840403+00:00
-- url     : https://prove2.me/submissions/bf4d2a69-93b0-4ee9-9b7c-dae171947bc0

import Definitions.Def_PrimorialCertData_21

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData21.q0 : PrimData21.s0.bok = true := by decide +kernel
theorem PrimData21.q1 : PrimData21.s1.bok = true := by decide +kernel
theorem PrimData21.q2 : PrimData21.s2.bok = true := by decide +kernel
theorem PrimData21.q3 : PrimData21.s3.bok = true := by decide +kernel
theorem PrimData21.q4 : PrimData21.s4.bok = true := by decide +kernel
theorem PrimData21.q5 : PrimData21.s5.bok = true := by decide +kernel
theorem PrimData21.q6 : PrimData21.s6.bok = true := by decide +kernel
theorem PrimData21.q7 : PrimData21.s7.bok = true := by decide +kernel
theorem PrimData21.q8 : PrimData21.s8.bok = true := by decide +kernel
theorem PrimData21.q9 : PrimData21.s9.bok = true := by decide +kernel
theorem PrimData21.q10 : PrimData21.s10.bok = true := by decide +kernel
theorem PrimData21.q11 : PrimData21.s11.bok = true := by decide +kernel
theorem PrimData21.q12 : PrimData21.s12.bok = true := by decide +kernel
theorem PrimData21.q13 : PrimData21.s13.bok = true := by decide +kernel
theorem PrimData21.q14 : PrimData21.s14.bok = true := by decide +kernel
theorem PrimData21.q15 : PrimData21.s15.bok = true := by decide +kernel
theorem PrimData21.q16 : PrimData21.s16.bok = true := by decide +kernel
theorem PrimData21.q17 : PrimData21.s17.bok = true := by decide +kernel
theorem PrimData21.q18 : PrimData21.s18.bok = true := by decide +kernel
theorem PrimData21.q19 : PrimData21.s19.bok = true := by decide +kernel
theorem PrimData21.q20 : PrimData21.s20.bok = true := by decide +kernel
theorem PrimData21.q21 : PrimData21.s21.bok = true := by decide +kernel
theorem PrimData21.q22 : PrimData21.s22.bok = true := by decide +kernel
theorem PrimData21.q23 : PrimData21.s23.bok = true := by decide +kernel
theorem PrimData21.q24 : PrimData21.s24.bok = true := by decide +kernel
theorem PrimData21.q25 : PrimData21.s25.bok = true := by decide +kernel
theorem PrimData21.q26 : PrimData21.s26.bok = true := by decide +kernel
theorem PrimData21.q27 : PrimData21.s27.bok = true := by decide +kernel
theorem PrimData21.q28 : PrimData21.s28.bok = true := by decide +kernel
theorem PrimData21.q29 : PrimData21.s29.bok = true := by decide +kernel
theorem PrimData21.q30 : PrimData21.s30.bok = true := by decide +kernel
theorem PrimData21.q31 : PrimData21.s31.bok = true := by decide +kernel
theorem PrimData21.q32 : PrimData21.s32.bok = true := by decide +kernel
theorem PrimData21.q33 : PrimData21.s33.bok = true := by decide +kernel
theorem PrimData21.q34 : PrimData21.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData21.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData21.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData21.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData21.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData21.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
