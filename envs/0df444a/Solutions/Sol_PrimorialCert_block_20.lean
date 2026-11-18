-- Prove2me | solution 1 for PrimorialCert.block_20
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:32.768906+00:00
-- url     : https://prove2.me/submissions/da73c8c3-828b-44c0-9752-5844479bffc5

import Definitions.Def_PrimorialCertData_20

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData20.q0 : PrimData20.s0.bok = true := by decide +kernel
theorem PrimData20.q1 : PrimData20.s1.bok = true := by decide +kernel
theorem PrimData20.q2 : PrimData20.s2.bok = true := by decide +kernel
theorem PrimData20.q3 : PrimData20.s3.bok = true := by decide +kernel
theorem PrimData20.q4 : PrimData20.s4.bok = true := by decide +kernel
theorem PrimData20.q5 : PrimData20.s5.bok = true := by decide +kernel
theorem PrimData20.q6 : PrimData20.s6.bok = true := by decide +kernel
theorem PrimData20.q7 : PrimData20.s7.bok = true := by decide +kernel
theorem PrimData20.q8 : PrimData20.s8.bok = true := by decide +kernel
theorem PrimData20.q9 : PrimData20.s9.bok = true := by decide +kernel
theorem PrimData20.q10 : PrimData20.s10.bok = true := by decide +kernel
theorem PrimData20.q11 : PrimData20.s11.bok = true := by decide +kernel
theorem PrimData20.q12 : PrimData20.s12.bok = true := by decide +kernel
theorem PrimData20.q13 : PrimData20.s13.bok = true := by decide +kernel
theorem PrimData20.q14 : PrimData20.s14.bok = true := by decide +kernel
theorem PrimData20.q15 : PrimData20.s15.bok = true := by decide +kernel
theorem PrimData20.q16 : PrimData20.s16.bok = true := by decide +kernel
theorem PrimData20.q17 : PrimData20.s17.bok = true := by decide +kernel
theorem PrimData20.q18 : PrimData20.s18.bok = true := by decide +kernel
theorem PrimData20.q19 : PrimData20.s19.bok = true := by decide +kernel
theorem PrimData20.q20 : PrimData20.s20.bok = true := by decide +kernel
theorem PrimData20.q21 : PrimData20.s21.bok = true := by decide +kernel
theorem PrimData20.q22 : PrimData20.s22.bok = true := by decide +kernel
theorem PrimData20.q23 : PrimData20.s23.bok = true := by decide +kernel
theorem PrimData20.q24 : PrimData20.s24.bok = true := by decide +kernel
theorem PrimData20.q25 : PrimData20.s25.bok = true := by decide +kernel
theorem PrimData20.q26 : PrimData20.s26.bok = true := by decide +kernel
theorem PrimData20.q27 : PrimData20.s27.bok = true := by decide +kernel
theorem PrimData20.q28 : PrimData20.s28.bok = true := by decide +kernel
theorem PrimData20.q29 : PrimData20.s29.bok = true := by decide +kernel
theorem PrimData20.q30 : PrimData20.s30.bok = true := by decide +kernel
theorem PrimData20.q31 : PrimData20.s31.bok = true := by decide +kernel
theorem PrimData20.q32 : PrimData20.s32.bok = true := by decide +kernel
theorem PrimData20.q33 : PrimData20.s33.bok = true := by decide +kernel
theorem PrimData20.q34 : PrimData20.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData20.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData20.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData20.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData20.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData20.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
