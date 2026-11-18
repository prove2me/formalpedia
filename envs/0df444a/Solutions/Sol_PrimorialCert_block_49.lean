-- Prove2me | solution 1 for PrimorialCert.block_49
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:29.03466+00:00
-- url     : https://prove2.me/submissions/4d508dd6-1b96-4cdd-b918-b202ca34b237

import Definitions.Def_PrimorialCertData_49

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData49.q0 : PrimData49.s0.bok = true := by decide +kernel
theorem PrimData49.q1 : PrimData49.s1.bok = true := by decide +kernel
theorem PrimData49.q2 : PrimData49.s2.bok = true := by decide +kernel
theorem PrimData49.q3 : PrimData49.s3.bok = true := by decide +kernel
theorem PrimData49.q4 : PrimData49.s4.bok = true := by decide +kernel
theorem PrimData49.q5 : PrimData49.s5.bok = true := by decide +kernel
theorem PrimData49.q6 : PrimData49.s6.bok = true := by decide +kernel
theorem PrimData49.q7 : PrimData49.s7.bok = true := by decide +kernel
theorem PrimData49.q8 : PrimData49.s8.bok = true := by decide +kernel
theorem PrimData49.q9 : PrimData49.s9.bok = true := by decide +kernel
theorem PrimData49.q10 : PrimData49.s10.bok = true := by decide +kernel
theorem PrimData49.q11 : PrimData49.s11.bok = true := by decide +kernel
theorem PrimData49.q12 : PrimData49.s12.bok = true := by decide +kernel
theorem PrimData49.q13 : PrimData49.s13.bok = true := by decide +kernel
theorem PrimData49.q14 : PrimData49.s14.bok = true := by decide +kernel
theorem PrimData49.q15 : PrimData49.s15.bok = true := by decide +kernel
theorem PrimData49.q16 : PrimData49.s16.bok = true := by decide +kernel
theorem PrimData49.q17 : PrimData49.s17.bok = true := by decide +kernel
theorem PrimData49.q18 : PrimData49.s18.bok = true := by decide +kernel
theorem PrimData49.q19 : PrimData49.s19.bok = true := by decide +kernel
theorem PrimData49.q20 : PrimData49.s20.bok = true := by decide +kernel
theorem PrimData49.q21 : PrimData49.s21.bok = true := by decide +kernel
theorem PrimData49.q22 : PrimData49.s22.bok = true := by decide +kernel
theorem PrimData49.q23 : PrimData49.s23.bok = true := by decide +kernel
theorem PrimData49.q24 : PrimData49.s24.bok = true := by decide +kernel
theorem PrimData49.q25 : PrimData49.s25.bok = true := by decide +kernel
theorem PrimData49.q26 : PrimData49.s26.bok = true := by decide +kernel
theorem PrimData49.q27 : PrimData49.s27.bok = true := by decide +kernel
theorem PrimData49.q28 : PrimData49.s28.bok = true := by decide +kernel
theorem PrimData49.q29 : PrimData49.s29.bok = true := by decide +kernel
theorem PrimData49.q30 : PrimData49.s30.bok = true := by decide +kernel
theorem PrimData49.q31 : PrimData49.s31.bok = true := by decide +kernel
theorem PrimData49.q32 : PrimData49.s32.bok = true := by decide +kernel
theorem PrimData49.q33 : PrimData49.s33.bok = true := by decide +kernel
theorem PrimData49.q34 : PrimData49.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData49.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData49.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData49.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData49.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData49.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
