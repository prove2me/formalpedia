-- Prove2me | solution 1 for PrimorialCert.block_67
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:30:05.247488+00:00
-- url     : https://prove2.me/submissions/6d845732-9fc9-40b4-9790-fedae52e749f

import Definitions.Def_PrimorialCertData_67

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData67.q0 : PrimData67.s0.bok = true := by decide +kernel
theorem PrimData67.q1 : PrimData67.s1.bok = true := by decide +kernel
theorem PrimData67.q2 : PrimData67.s2.bok = true := by decide +kernel
theorem PrimData67.q3 : PrimData67.s3.bok = true := by decide +kernel
theorem PrimData67.q4 : PrimData67.s4.bok = true := by decide +kernel
theorem PrimData67.q5 : PrimData67.s5.bok = true := by decide +kernel
theorem PrimData67.q6 : PrimData67.s6.bok = true := by decide +kernel
theorem PrimData67.q7 : PrimData67.s7.bok = true := by decide +kernel
theorem PrimData67.q8 : PrimData67.s8.bok = true := by decide +kernel
theorem PrimData67.q9 : PrimData67.s9.bok = true := by decide +kernel
theorem PrimData67.q10 : PrimData67.s10.bok = true := by decide +kernel
theorem PrimData67.q11 : PrimData67.s11.bok = true := by decide +kernel
theorem PrimData67.q12 : PrimData67.s12.bok = true := by decide +kernel
theorem PrimData67.q13 : PrimData67.s13.bok = true := by decide +kernel
theorem PrimData67.q14 : PrimData67.s14.bok = true := by decide +kernel
theorem PrimData67.q15 : PrimData67.s15.bok = true := by decide +kernel
theorem PrimData67.q16 : PrimData67.s16.bok = true := by decide +kernel
theorem PrimData67.q17 : PrimData67.s17.bok = true := by decide +kernel
theorem PrimData67.q18 : PrimData67.s18.bok = true := by decide +kernel
theorem PrimData67.q19 : PrimData67.s19.bok = true := by decide +kernel
theorem PrimData67.q20 : PrimData67.s20.bok = true := by decide +kernel
theorem PrimData67.q21 : PrimData67.s21.bok = true := by decide +kernel
theorem PrimData67.q22 : PrimData67.s22.bok = true := by decide +kernel
theorem PrimData67.q23 : PrimData67.s23.bok = true := by decide +kernel
theorem PrimData67.q24 : PrimData67.s24.bok = true := by decide +kernel
theorem PrimData67.q25 : PrimData67.s25.bok = true := by decide +kernel
theorem PrimData67.q26 : PrimData67.s26.bok = true := by decide +kernel
theorem PrimData67.q27 : PrimData67.s27.bok = true := by decide +kernel
theorem PrimData67.q28 : PrimData67.s28.bok = true := by decide +kernel
theorem PrimData67.q29 : PrimData67.s29.bok = true := by decide +kernel
theorem PrimData67.q30 : PrimData67.s30.bok = true := by decide +kernel
theorem PrimData67.q31 : PrimData67.s31.bok = true := by decide +kernel
theorem PrimData67.q32 : PrimData67.s32.bok = true := by decide +kernel
theorem PrimData67.q33 : PrimData67.s33.bok = true := by decide +kernel
theorem PrimData67.q34 : PrimData67.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData67.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData67.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData67.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData67.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData67.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
