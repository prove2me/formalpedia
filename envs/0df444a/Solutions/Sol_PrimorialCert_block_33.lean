-- Prove2me | solution 1 for PrimorialCert.block_33
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:58.909667+00:00
-- url     : https://prove2.me/submissions/49a28058-e4ba-486d-a566-deee1ec96dd5

import Definitions.Def_PrimorialCertData_33

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData33.q0 : PrimData33.s0.bok = true := by decide +kernel
theorem PrimData33.q1 : PrimData33.s1.bok = true := by decide +kernel
theorem PrimData33.q2 : PrimData33.s2.bok = true := by decide +kernel
theorem PrimData33.q3 : PrimData33.s3.bok = true := by decide +kernel
theorem PrimData33.q4 : PrimData33.s4.bok = true := by decide +kernel
theorem PrimData33.q5 : PrimData33.s5.bok = true := by decide +kernel
theorem PrimData33.q6 : PrimData33.s6.bok = true := by decide +kernel
theorem PrimData33.q7 : PrimData33.s7.bok = true := by decide +kernel
theorem PrimData33.q8 : PrimData33.s8.bok = true := by decide +kernel
theorem PrimData33.q9 : PrimData33.s9.bok = true := by decide +kernel
theorem PrimData33.q10 : PrimData33.s10.bok = true := by decide +kernel
theorem PrimData33.q11 : PrimData33.s11.bok = true := by decide +kernel
theorem PrimData33.q12 : PrimData33.s12.bok = true := by decide +kernel
theorem PrimData33.q13 : PrimData33.s13.bok = true := by decide +kernel
theorem PrimData33.q14 : PrimData33.s14.bok = true := by decide +kernel
theorem PrimData33.q15 : PrimData33.s15.bok = true := by decide +kernel
theorem PrimData33.q16 : PrimData33.s16.bok = true := by decide +kernel
theorem PrimData33.q17 : PrimData33.s17.bok = true := by decide +kernel
theorem PrimData33.q18 : PrimData33.s18.bok = true := by decide +kernel
theorem PrimData33.q19 : PrimData33.s19.bok = true := by decide +kernel
theorem PrimData33.q20 : PrimData33.s20.bok = true := by decide +kernel
theorem PrimData33.q21 : PrimData33.s21.bok = true := by decide +kernel
theorem PrimData33.q22 : PrimData33.s22.bok = true := by decide +kernel
theorem PrimData33.q23 : PrimData33.s23.bok = true := by decide +kernel
theorem PrimData33.q24 : PrimData33.s24.bok = true := by decide +kernel
theorem PrimData33.q25 : PrimData33.s25.bok = true := by decide +kernel
theorem PrimData33.q26 : PrimData33.s26.bok = true := by decide +kernel
theorem PrimData33.q27 : PrimData33.s27.bok = true := by decide +kernel
theorem PrimData33.q28 : PrimData33.s28.bok = true := by decide +kernel
theorem PrimData33.q29 : PrimData33.s29.bok = true := by decide +kernel
theorem PrimData33.q30 : PrimData33.s30.bok = true := by decide +kernel
theorem PrimData33.q31 : PrimData33.s31.bok = true := by decide +kernel
theorem PrimData33.q32 : PrimData33.s32.bok = true := by decide +kernel
theorem PrimData33.q33 : PrimData33.s33.bok = true := by decide +kernel
theorem PrimData33.q34 : PrimData33.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData33.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData33.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData33.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData33.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData33.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
