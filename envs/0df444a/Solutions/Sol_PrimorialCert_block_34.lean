-- Prove2me | solution 1 for PrimorialCert.block_34
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:01.014204+00:00
-- url     : https://prove2.me/submissions/22824d97-2b7a-4753-be42-e50b9cc33766

import Definitions.Def_PrimorialCertData_34

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData34.q0 : PrimData34.s0.bok = true := by decide +kernel
theorem PrimData34.q1 : PrimData34.s1.bok = true := by decide +kernel
theorem PrimData34.q2 : PrimData34.s2.bok = true := by decide +kernel
theorem PrimData34.q3 : PrimData34.s3.bok = true := by decide +kernel
theorem PrimData34.q4 : PrimData34.s4.bok = true := by decide +kernel
theorem PrimData34.q5 : PrimData34.s5.bok = true := by decide +kernel
theorem PrimData34.q6 : PrimData34.s6.bok = true := by decide +kernel
theorem PrimData34.q7 : PrimData34.s7.bok = true := by decide +kernel
theorem PrimData34.q8 : PrimData34.s8.bok = true := by decide +kernel
theorem PrimData34.q9 : PrimData34.s9.bok = true := by decide +kernel
theorem PrimData34.q10 : PrimData34.s10.bok = true := by decide +kernel
theorem PrimData34.q11 : PrimData34.s11.bok = true := by decide +kernel
theorem PrimData34.q12 : PrimData34.s12.bok = true := by decide +kernel
theorem PrimData34.q13 : PrimData34.s13.bok = true := by decide +kernel
theorem PrimData34.q14 : PrimData34.s14.bok = true := by decide +kernel
theorem PrimData34.q15 : PrimData34.s15.bok = true := by decide +kernel
theorem PrimData34.q16 : PrimData34.s16.bok = true := by decide +kernel
theorem PrimData34.q17 : PrimData34.s17.bok = true := by decide +kernel
theorem PrimData34.q18 : PrimData34.s18.bok = true := by decide +kernel
theorem PrimData34.q19 : PrimData34.s19.bok = true := by decide +kernel
theorem PrimData34.q20 : PrimData34.s20.bok = true := by decide +kernel
theorem PrimData34.q21 : PrimData34.s21.bok = true := by decide +kernel
theorem PrimData34.q22 : PrimData34.s22.bok = true := by decide +kernel
theorem PrimData34.q23 : PrimData34.s23.bok = true := by decide +kernel
theorem PrimData34.q24 : PrimData34.s24.bok = true := by decide +kernel
theorem PrimData34.q25 : PrimData34.s25.bok = true := by decide +kernel
theorem PrimData34.q26 : PrimData34.s26.bok = true := by decide +kernel
theorem PrimData34.q27 : PrimData34.s27.bok = true := by decide +kernel
theorem PrimData34.q28 : PrimData34.s28.bok = true := by decide +kernel
theorem PrimData34.q29 : PrimData34.s29.bok = true := by decide +kernel
theorem PrimData34.q30 : PrimData34.s30.bok = true := by decide +kernel
theorem PrimData34.q31 : PrimData34.s31.bok = true := by decide +kernel
theorem PrimData34.q32 : PrimData34.s32.bok = true := by decide +kernel
theorem PrimData34.q33 : PrimData34.s33.bok = true := by decide +kernel
theorem PrimData34.q34 : PrimData34.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData34.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData34.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData34.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData34.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData34.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
