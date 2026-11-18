-- Prove2me | solution 1 for PrimorialCert.block_30
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:52.861194+00:00
-- url     : https://prove2.me/submissions/14ec8965-a1a7-4efc-8111-30f2905c621e

import Definitions.Def_PrimorialCertData_30

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData30.q0 : PrimData30.s0.bok = true := by decide +kernel
theorem PrimData30.q1 : PrimData30.s1.bok = true := by decide +kernel
theorem PrimData30.q2 : PrimData30.s2.bok = true := by decide +kernel
theorem PrimData30.q3 : PrimData30.s3.bok = true := by decide +kernel
theorem PrimData30.q4 : PrimData30.s4.bok = true := by decide +kernel
theorem PrimData30.q5 : PrimData30.s5.bok = true := by decide +kernel
theorem PrimData30.q6 : PrimData30.s6.bok = true := by decide +kernel
theorem PrimData30.q7 : PrimData30.s7.bok = true := by decide +kernel
theorem PrimData30.q8 : PrimData30.s8.bok = true := by decide +kernel
theorem PrimData30.q9 : PrimData30.s9.bok = true := by decide +kernel
theorem PrimData30.q10 : PrimData30.s10.bok = true := by decide +kernel
theorem PrimData30.q11 : PrimData30.s11.bok = true := by decide +kernel
theorem PrimData30.q12 : PrimData30.s12.bok = true := by decide +kernel
theorem PrimData30.q13 : PrimData30.s13.bok = true := by decide +kernel
theorem PrimData30.q14 : PrimData30.s14.bok = true := by decide +kernel
theorem PrimData30.q15 : PrimData30.s15.bok = true := by decide +kernel
theorem PrimData30.q16 : PrimData30.s16.bok = true := by decide +kernel
theorem PrimData30.q17 : PrimData30.s17.bok = true := by decide +kernel
theorem PrimData30.q18 : PrimData30.s18.bok = true := by decide +kernel
theorem PrimData30.q19 : PrimData30.s19.bok = true := by decide +kernel
theorem PrimData30.q20 : PrimData30.s20.bok = true := by decide +kernel
theorem PrimData30.q21 : PrimData30.s21.bok = true := by decide +kernel
theorem PrimData30.q22 : PrimData30.s22.bok = true := by decide +kernel
theorem PrimData30.q23 : PrimData30.s23.bok = true := by decide +kernel
theorem PrimData30.q24 : PrimData30.s24.bok = true := by decide +kernel
theorem PrimData30.q25 : PrimData30.s25.bok = true := by decide +kernel
theorem PrimData30.q26 : PrimData30.s26.bok = true := by decide +kernel
theorem PrimData30.q27 : PrimData30.s27.bok = true := by decide +kernel
theorem PrimData30.q28 : PrimData30.s28.bok = true := by decide +kernel
theorem PrimData30.q29 : PrimData30.s29.bok = true := by decide +kernel
theorem PrimData30.q30 : PrimData30.s30.bok = true := by decide +kernel
theorem PrimData30.q31 : PrimData30.s31.bok = true := by decide +kernel
theorem PrimData30.q32 : PrimData30.s32.bok = true := by decide +kernel
theorem PrimData30.q33 : PrimData30.s33.bok = true := by decide +kernel
theorem PrimData30.q34 : PrimData30.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData30.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData30.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData30.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData30.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData30.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
