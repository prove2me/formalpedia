-- Prove2me | solution 1 for PrimorialCert.block_36
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:04.940818+00:00
-- url     : https://prove2.me/submissions/c09f49e0-b107-41d8-a29e-84281198f44f

import Definitions.Def_PrimorialCertData_36

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData36.q0 : PrimData36.s0.bok = true := by decide +kernel
theorem PrimData36.q1 : PrimData36.s1.bok = true := by decide +kernel
theorem PrimData36.q2 : PrimData36.s2.bok = true := by decide +kernel
theorem PrimData36.q3 : PrimData36.s3.bok = true := by decide +kernel
theorem PrimData36.q4 : PrimData36.s4.bok = true := by decide +kernel
theorem PrimData36.q5 : PrimData36.s5.bok = true := by decide +kernel
theorem PrimData36.q6 : PrimData36.s6.bok = true := by decide +kernel
theorem PrimData36.q7 : PrimData36.s7.bok = true := by decide +kernel
theorem PrimData36.q8 : PrimData36.s8.bok = true := by decide +kernel
theorem PrimData36.q9 : PrimData36.s9.bok = true := by decide +kernel
theorem PrimData36.q10 : PrimData36.s10.bok = true := by decide +kernel
theorem PrimData36.q11 : PrimData36.s11.bok = true := by decide +kernel
theorem PrimData36.q12 : PrimData36.s12.bok = true := by decide +kernel
theorem PrimData36.q13 : PrimData36.s13.bok = true := by decide +kernel
theorem PrimData36.q14 : PrimData36.s14.bok = true := by decide +kernel
theorem PrimData36.q15 : PrimData36.s15.bok = true := by decide +kernel
theorem PrimData36.q16 : PrimData36.s16.bok = true := by decide +kernel
theorem PrimData36.q17 : PrimData36.s17.bok = true := by decide +kernel
theorem PrimData36.q18 : PrimData36.s18.bok = true := by decide +kernel
theorem PrimData36.q19 : PrimData36.s19.bok = true := by decide +kernel
theorem PrimData36.q20 : PrimData36.s20.bok = true := by decide +kernel
theorem PrimData36.q21 : PrimData36.s21.bok = true := by decide +kernel
theorem PrimData36.q22 : PrimData36.s22.bok = true := by decide +kernel
theorem PrimData36.q23 : PrimData36.s23.bok = true := by decide +kernel
theorem PrimData36.q24 : PrimData36.s24.bok = true := by decide +kernel
theorem PrimData36.q25 : PrimData36.s25.bok = true := by decide +kernel
theorem PrimData36.q26 : PrimData36.s26.bok = true := by decide +kernel
theorem PrimData36.q27 : PrimData36.s27.bok = true := by decide +kernel
theorem PrimData36.q28 : PrimData36.s28.bok = true := by decide +kernel
theorem PrimData36.q29 : PrimData36.s29.bok = true := by decide +kernel
theorem PrimData36.q30 : PrimData36.s30.bok = true := by decide +kernel
theorem PrimData36.q31 : PrimData36.s31.bok = true := by decide +kernel
theorem PrimData36.q32 : PrimData36.s32.bok = true := by decide +kernel
theorem PrimData36.q33 : PrimData36.s33.bok = true := by decide +kernel
theorem PrimData36.q34 : PrimData36.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData36.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData36.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData36.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData36.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData36.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
