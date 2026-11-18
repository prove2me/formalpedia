-- Prove2me | solution 1 for PrimorialCert.block_48
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:27.110018+00:00
-- url     : https://prove2.me/submissions/5a4825c9-e7bc-46a9-a150-2c593cd1fc89

import Definitions.Def_PrimorialCertData_48

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData48.q0 : PrimData48.s0.bok = true := by decide +kernel
theorem PrimData48.q1 : PrimData48.s1.bok = true := by decide +kernel
theorem PrimData48.q2 : PrimData48.s2.bok = true := by decide +kernel
theorem PrimData48.q3 : PrimData48.s3.bok = true := by decide +kernel
theorem PrimData48.q4 : PrimData48.s4.bok = true := by decide +kernel
theorem PrimData48.q5 : PrimData48.s5.bok = true := by decide +kernel
theorem PrimData48.q6 : PrimData48.s6.bok = true := by decide +kernel
theorem PrimData48.q7 : PrimData48.s7.bok = true := by decide +kernel
theorem PrimData48.q8 : PrimData48.s8.bok = true := by decide +kernel
theorem PrimData48.q9 : PrimData48.s9.bok = true := by decide +kernel
theorem PrimData48.q10 : PrimData48.s10.bok = true := by decide +kernel
theorem PrimData48.q11 : PrimData48.s11.bok = true := by decide +kernel
theorem PrimData48.q12 : PrimData48.s12.bok = true := by decide +kernel
theorem PrimData48.q13 : PrimData48.s13.bok = true := by decide +kernel
theorem PrimData48.q14 : PrimData48.s14.bok = true := by decide +kernel
theorem PrimData48.q15 : PrimData48.s15.bok = true := by decide +kernel
theorem PrimData48.q16 : PrimData48.s16.bok = true := by decide +kernel
theorem PrimData48.q17 : PrimData48.s17.bok = true := by decide +kernel
theorem PrimData48.q18 : PrimData48.s18.bok = true := by decide +kernel
theorem PrimData48.q19 : PrimData48.s19.bok = true := by decide +kernel
theorem PrimData48.q20 : PrimData48.s20.bok = true := by decide +kernel
theorem PrimData48.q21 : PrimData48.s21.bok = true := by decide +kernel
theorem PrimData48.q22 : PrimData48.s22.bok = true := by decide +kernel
theorem PrimData48.q23 : PrimData48.s23.bok = true := by decide +kernel
theorem PrimData48.q24 : PrimData48.s24.bok = true := by decide +kernel
theorem PrimData48.q25 : PrimData48.s25.bok = true := by decide +kernel
theorem PrimData48.q26 : PrimData48.s26.bok = true := by decide +kernel
theorem PrimData48.q27 : PrimData48.s27.bok = true := by decide +kernel
theorem PrimData48.q28 : PrimData48.s28.bok = true := by decide +kernel
theorem PrimData48.q29 : PrimData48.s29.bok = true := by decide +kernel
theorem PrimData48.q30 : PrimData48.s30.bok = true := by decide +kernel
theorem PrimData48.q31 : PrimData48.s31.bok = true := by decide +kernel
theorem PrimData48.q32 : PrimData48.s32.bok = true := by decide +kernel
theorem PrimData48.q33 : PrimData48.s33.bok = true := by decide +kernel
theorem PrimData48.q34 : PrimData48.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData48.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData48.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData48.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData48.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData48.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
