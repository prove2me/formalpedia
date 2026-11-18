-- Prove2me | solution 1 for PrimorialCert.block_63
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:57.167839+00:00
-- url     : https://prove2.me/submissions/8407711f-510b-4a58-98ef-0e927560f1eb

import Definitions.Def_PrimorialCertData_63

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData63.q0 : PrimData63.s0.bok = true := by decide +kernel
theorem PrimData63.q1 : PrimData63.s1.bok = true := by decide +kernel
theorem PrimData63.q2 : PrimData63.s2.bok = true := by decide +kernel
theorem PrimData63.q3 : PrimData63.s3.bok = true := by decide +kernel
theorem PrimData63.q4 : PrimData63.s4.bok = true := by decide +kernel
theorem PrimData63.q5 : PrimData63.s5.bok = true := by decide +kernel
theorem PrimData63.q6 : PrimData63.s6.bok = true := by decide +kernel
theorem PrimData63.q7 : PrimData63.s7.bok = true := by decide +kernel
theorem PrimData63.q8 : PrimData63.s8.bok = true := by decide +kernel
theorem PrimData63.q9 : PrimData63.s9.bok = true := by decide +kernel
theorem PrimData63.q10 : PrimData63.s10.bok = true := by decide +kernel
theorem PrimData63.q11 : PrimData63.s11.bok = true := by decide +kernel
theorem PrimData63.q12 : PrimData63.s12.bok = true := by decide +kernel
theorem PrimData63.q13 : PrimData63.s13.bok = true := by decide +kernel
theorem PrimData63.q14 : PrimData63.s14.bok = true := by decide +kernel
theorem PrimData63.q15 : PrimData63.s15.bok = true := by decide +kernel
theorem PrimData63.q16 : PrimData63.s16.bok = true := by decide +kernel
theorem PrimData63.q17 : PrimData63.s17.bok = true := by decide +kernel
theorem PrimData63.q18 : PrimData63.s18.bok = true := by decide +kernel
theorem PrimData63.q19 : PrimData63.s19.bok = true := by decide +kernel
theorem PrimData63.q20 : PrimData63.s20.bok = true := by decide +kernel
theorem PrimData63.q21 : PrimData63.s21.bok = true := by decide +kernel
theorem PrimData63.q22 : PrimData63.s22.bok = true := by decide +kernel
theorem PrimData63.q23 : PrimData63.s23.bok = true := by decide +kernel
theorem PrimData63.q24 : PrimData63.s24.bok = true := by decide +kernel
theorem PrimData63.q25 : PrimData63.s25.bok = true := by decide +kernel
theorem PrimData63.q26 : PrimData63.s26.bok = true := by decide +kernel
theorem PrimData63.q27 : PrimData63.s27.bok = true := by decide +kernel
theorem PrimData63.q28 : PrimData63.s28.bok = true := by decide +kernel
theorem PrimData63.q29 : PrimData63.s29.bok = true := by decide +kernel
theorem PrimData63.q30 : PrimData63.s30.bok = true := by decide +kernel
theorem PrimData63.q31 : PrimData63.s31.bok = true := by decide +kernel
theorem PrimData63.q32 : PrimData63.s32.bok = true := by decide +kernel
theorem PrimData63.q33 : PrimData63.s33.bok = true := by decide +kernel
theorem PrimData63.q34 : PrimData63.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData63.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData63.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData63.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData63.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData63.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
