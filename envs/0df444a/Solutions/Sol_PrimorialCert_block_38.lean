-- Prove2me | solution 1 for PrimorialCert.block_38
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:08.966031+00:00
-- url     : https://prove2.me/submissions/d10f090c-c14f-4e3c-887a-c2b707dd87dc

import Definitions.Def_PrimorialCertData_38

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData38.q0 : PrimData38.s0.bok = true := by decide +kernel
theorem PrimData38.q1 : PrimData38.s1.bok = true := by decide +kernel
theorem PrimData38.q2 : PrimData38.s2.bok = true := by decide +kernel
theorem PrimData38.q3 : PrimData38.s3.bok = true := by decide +kernel
theorem PrimData38.q4 : PrimData38.s4.bok = true := by decide +kernel
theorem PrimData38.q5 : PrimData38.s5.bok = true := by decide +kernel
theorem PrimData38.q6 : PrimData38.s6.bok = true := by decide +kernel
theorem PrimData38.q7 : PrimData38.s7.bok = true := by decide +kernel
theorem PrimData38.q8 : PrimData38.s8.bok = true := by decide +kernel
theorem PrimData38.q9 : PrimData38.s9.bok = true := by decide +kernel
theorem PrimData38.q10 : PrimData38.s10.bok = true := by decide +kernel
theorem PrimData38.q11 : PrimData38.s11.bok = true := by decide +kernel
theorem PrimData38.q12 : PrimData38.s12.bok = true := by decide +kernel
theorem PrimData38.q13 : PrimData38.s13.bok = true := by decide +kernel
theorem PrimData38.q14 : PrimData38.s14.bok = true := by decide +kernel
theorem PrimData38.q15 : PrimData38.s15.bok = true := by decide +kernel
theorem PrimData38.q16 : PrimData38.s16.bok = true := by decide +kernel
theorem PrimData38.q17 : PrimData38.s17.bok = true := by decide +kernel
theorem PrimData38.q18 : PrimData38.s18.bok = true := by decide +kernel
theorem PrimData38.q19 : PrimData38.s19.bok = true := by decide +kernel
theorem PrimData38.q20 : PrimData38.s20.bok = true := by decide +kernel
theorem PrimData38.q21 : PrimData38.s21.bok = true := by decide +kernel
theorem PrimData38.q22 : PrimData38.s22.bok = true := by decide +kernel
theorem PrimData38.q23 : PrimData38.s23.bok = true := by decide +kernel
theorem PrimData38.q24 : PrimData38.s24.bok = true := by decide +kernel
theorem PrimData38.q25 : PrimData38.s25.bok = true := by decide +kernel
theorem PrimData38.q26 : PrimData38.s26.bok = true := by decide +kernel
theorem PrimData38.q27 : PrimData38.s27.bok = true := by decide +kernel
theorem PrimData38.q28 : PrimData38.s28.bok = true := by decide +kernel
theorem PrimData38.q29 : PrimData38.s29.bok = true := by decide +kernel
theorem PrimData38.q30 : PrimData38.s30.bok = true := by decide +kernel
theorem PrimData38.q31 : PrimData38.s31.bok = true := by decide +kernel
theorem PrimData38.q32 : PrimData38.s32.bok = true := by decide +kernel
theorem PrimData38.q33 : PrimData38.s33.bok = true := by decide +kernel
theorem PrimData38.q34 : PrimData38.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData38.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData38.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData38.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData38.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData38.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
