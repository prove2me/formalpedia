-- Prove2me | solution 1 for PrimorialCert.block_65
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:01.162755+00:00
-- url     : https://prove2.me/submissions/a5937eff-e5dd-41fc-b425-3f56e40cb5cf

import Definitions.Def_PrimorialCertData_65

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData65.q0 : PrimData65.s0.bok = true := by decide +kernel
theorem PrimData65.q1 : PrimData65.s1.bok = true := by decide +kernel
theorem PrimData65.q2 : PrimData65.s2.bok = true := by decide +kernel
theorem PrimData65.q3 : PrimData65.s3.bok = true := by decide +kernel
theorem PrimData65.q4 : PrimData65.s4.bok = true := by decide +kernel
theorem PrimData65.q5 : PrimData65.s5.bok = true := by decide +kernel
theorem PrimData65.q6 : PrimData65.s6.bok = true := by decide +kernel
theorem PrimData65.q7 : PrimData65.s7.bok = true := by decide +kernel
theorem PrimData65.q8 : PrimData65.s8.bok = true := by decide +kernel
theorem PrimData65.q9 : PrimData65.s9.bok = true := by decide +kernel
theorem PrimData65.q10 : PrimData65.s10.bok = true := by decide +kernel
theorem PrimData65.q11 : PrimData65.s11.bok = true := by decide +kernel
theorem PrimData65.q12 : PrimData65.s12.bok = true := by decide +kernel
theorem PrimData65.q13 : PrimData65.s13.bok = true := by decide +kernel
theorem PrimData65.q14 : PrimData65.s14.bok = true := by decide +kernel
theorem PrimData65.q15 : PrimData65.s15.bok = true := by decide +kernel
theorem PrimData65.q16 : PrimData65.s16.bok = true := by decide +kernel
theorem PrimData65.q17 : PrimData65.s17.bok = true := by decide +kernel
theorem PrimData65.q18 : PrimData65.s18.bok = true := by decide +kernel
theorem PrimData65.q19 : PrimData65.s19.bok = true := by decide +kernel
theorem PrimData65.q20 : PrimData65.s20.bok = true := by decide +kernel
theorem PrimData65.q21 : PrimData65.s21.bok = true := by decide +kernel
theorem PrimData65.q22 : PrimData65.s22.bok = true := by decide +kernel
theorem PrimData65.q23 : PrimData65.s23.bok = true := by decide +kernel
theorem PrimData65.q24 : PrimData65.s24.bok = true := by decide +kernel
theorem PrimData65.q25 : PrimData65.s25.bok = true := by decide +kernel
theorem PrimData65.q26 : PrimData65.s26.bok = true := by decide +kernel
theorem PrimData65.q27 : PrimData65.s27.bok = true := by decide +kernel
theorem PrimData65.q28 : PrimData65.s28.bok = true := by decide +kernel
theorem PrimData65.q29 : PrimData65.s29.bok = true := by decide +kernel
theorem PrimData65.q30 : PrimData65.s30.bok = true := by decide +kernel
theorem PrimData65.q31 : PrimData65.s31.bok = true := by decide +kernel
theorem PrimData65.q32 : PrimData65.s32.bok = true := by decide +kernel
theorem PrimData65.q33 : PrimData65.s33.bok = true := by decide +kernel
theorem PrimData65.q34 : PrimData65.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData65.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData65.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData65.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData65.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData65.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
