-- Prove2me | solution 1 for PrimorialCert.block_18
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:28.775541+00:00
-- url     : https://prove2.me/submissions/4cfb99f2-cc0d-41c6-867d-0e4f25312275

import Definitions.Def_PrimorialCertData_18

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData18.q0 : PrimData18.s0.bok = true := by decide +kernel
theorem PrimData18.q1 : PrimData18.s1.bok = true := by decide +kernel
theorem PrimData18.q2 : PrimData18.s2.bok = true := by decide +kernel
theorem PrimData18.q3 : PrimData18.s3.bok = true := by decide +kernel
theorem PrimData18.q4 : PrimData18.s4.bok = true := by decide +kernel
theorem PrimData18.q5 : PrimData18.s5.bok = true := by decide +kernel
theorem PrimData18.q6 : PrimData18.s6.bok = true := by decide +kernel
theorem PrimData18.q7 : PrimData18.s7.bok = true := by decide +kernel
theorem PrimData18.q8 : PrimData18.s8.bok = true := by decide +kernel
theorem PrimData18.q9 : PrimData18.s9.bok = true := by decide +kernel
theorem PrimData18.q10 : PrimData18.s10.bok = true := by decide +kernel
theorem PrimData18.q11 : PrimData18.s11.bok = true := by decide +kernel
theorem PrimData18.q12 : PrimData18.s12.bok = true := by decide +kernel
theorem PrimData18.q13 : PrimData18.s13.bok = true := by decide +kernel
theorem PrimData18.q14 : PrimData18.s14.bok = true := by decide +kernel
theorem PrimData18.q15 : PrimData18.s15.bok = true := by decide +kernel
theorem PrimData18.q16 : PrimData18.s16.bok = true := by decide +kernel
theorem PrimData18.q17 : PrimData18.s17.bok = true := by decide +kernel
theorem PrimData18.q18 : PrimData18.s18.bok = true := by decide +kernel
theorem PrimData18.q19 : PrimData18.s19.bok = true := by decide +kernel
theorem PrimData18.q20 : PrimData18.s20.bok = true := by decide +kernel
theorem PrimData18.q21 : PrimData18.s21.bok = true := by decide +kernel
theorem PrimData18.q22 : PrimData18.s22.bok = true := by decide +kernel
theorem PrimData18.q23 : PrimData18.s23.bok = true := by decide +kernel
theorem PrimData18.q24 : PrimData18.s24.bok = true := by decide +kernel
theorem PrimData18.q25 : PrimData18.s25.bok = true := by decide +kernel
theorem PrimData18.q26 : PrimData18.s26.bok = true := by decide +kernel
theorem PrimData18.q27 : PrimData18.s27.bok = true := by decide +kernel
theorem PrimData18.q28 : PrimData18.s28.bok = true := by decide +kernel
theorem PrimData18.q29 : PrimData18.s29.bok = true := by decide +kernel
theorem PrimData18.q30 : PrimData18.s30.bok = true := by decide +kernel
theorem PrimData18.q31 : PrimData18.s31.bok = true := by decide +kernel
theorem PrimData18.q32 : PrimData18.s32.bok = true := by decide +kernel
theorem PrimData18.q33 : PrimData18.s33.bok = true := by decide +kernel
theorem PrimData18.q34 : PrimData18.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData18.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData18.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData18.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData18.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData18.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
