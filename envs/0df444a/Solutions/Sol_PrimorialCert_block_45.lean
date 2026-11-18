-- Prove2me | solution 1 for PrimorialCert.block_45
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:21.0012+00:00
-- url     : https://prove2.me/submissions/58a74013-4658-4432-9a11-54efb7f9e6d1

import Definitions.Def_PrimorialCertData_45

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData45.q0 : PrimData45.s0.bok = true := by decide +kernel
theorem PrimData45.q1 : PrimData45.s1.bok = true := by decide +kernel
theorem PrimData45.q2 : PrimData45.s2.bok = true := by decide +kernel
theorem PrimData45.q3 : PrimData45.s3.bok = true := by decide +kernel
theorem PrimData45.q4 : PrimData45.s4.bok = true := by decide +kernel
theorem PrimData45.q5 : PrimData45.s5.bok = true := by decide +kernel
theorem PrimData45.q6 : PrimData45.s6.bok = true := by decide +kernel
theorem PrimData45.q7 : PrimData45.s7.bok = true := by decide +kernel
theorem PrimData45.q8 : PrimData45.s8.bok = true := by decide +kernel
theorem PrimData45.q9 : PrimData45.s9.bok = true := by decide +kernel
theorem PrimData45.q10 : PrimData45.s10.bok = true := by decide +kernel
theorem PrimData45.q11 : PrimData45.s11.bok = true := by decide +kernel
theorem PrimData45.q12 : PrimData45.s12.bok = true := by decide +kernel
theorem PrimData45.q13 : PrimData45.s13.bok = true := by decide +kernel
theorem PrimData45.q14 : PrimData45.s14.bok = true := by decide +kernel
theorem PrimData45.q15 : PrimData45.s15.bok = true := by decide +kernel
theorem PrimData45.q16 : PrimData45.s16.bok = true := by decide +kernel
theorem PrimData45.q17 : PrimData45.s17.bok = true := by decide +kernel
theorem PrimData45.q18 : PrimData45.s18.bok = true := by decide +kernel
theorem PrimData45.q19 : PrimData45.s19.bok = true := by decide +kernel
theorem PrimData45.q20 : PrimData45.s20.bok = true := by decide +kernel
theorem PrimData45.q21 : PrimData45.s21.bok = true := by decide +kernel
theorem PrimData45.q22 : PrimData45.s22.bok = true := by decide +kernel
theorem PrimData45.q23 : PrimData45.s23.bok = true := by decide +kernel
theorem PrimData45.q24 : PrimData45.s24.bok = true := by decide +kernel
theorem PrimData45.q25 : PrimData45.s25.bok = true := by decide +kernel
theorem PrimData45.q26 : PrimData45.s26.bok = true := by decide +kernel
theorem PrimData45.q27 : PrimData45.s27.bok = true := by decide +kernel
theorem PrimData45.q28 : PrimData45.s28.bok = true := by decide +kernel
theorem PrimData45.q29 : PrimData45.s29.bok = true := by decide +kernel
theorem PrimData45.q30 : PrimData45.s30.bok = true := by decide +kernel
theorem PrimData45.q31 : PrimData45.s31.bok = true := by decide +kernel
theorem PrimData45.q32 : PrimData45.s32.bok = true := by decide +kernel
theorem PrimData45.q33 : PrimData45.s33.bok = true := by decide +kernel
theorem PrimData45.q34 : PrimData45.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData45.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData45.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData45.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData45.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData45.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
