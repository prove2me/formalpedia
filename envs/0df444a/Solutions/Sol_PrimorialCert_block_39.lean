-- Prove2me | solution 1 for PrimorialCert.block_39
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:29:11.001143+00:00
-- url     : https://prove2.me/submissions/7178d139-dea0-4899-8129-cb0fc85f009b

import Definitions.Def_PrimorialCertData_39

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData39.q0 : PrimData39.s0.bok = true := by decide +kernel
theorem PrimData39.q1 : PrimData39.s1.bok = true := by decide +kernel
theorem PrimData39.q2 : PrimData39.s2.bok = true := by decide +kernel
theorem PrimData39.q3 : PrimData39.s3.bok = true := by decide +kernel
theorem PrimData39.q4 : PrimData39.s4.bok = true := by decide +kernel
theorem PrimData39.q5 : PrimData39.s5.bok = true := by decide +kernel
theorem PrimData39.q6 : PrimData39.s6.bok = true := by decide +kernel
theorem PrimData39.q7 : PrimData39.s7.bok = true := by decide +kernel
theorem PrimData39.q8 : PrimData39.s8.bok = true := by decide +kernel
theorem PrimData39.q9 : PrimData39.s9.bok = true := by decide +kernel
theorem PrimData39.q10 : PrimData39.s10.bok = true := by decide +kernel
theorem PrimData39.q11 : PrimData39.s11.bok = true := by decide +kernel
theorem PrimData39.q12 : PrimData39.s12.bok = true := by decide +kernel
theorem PrimData39.q13 : PrimData39.s13.bok = true := by decide +kernel
theorem PrimData39.q14 : PrimData39.s14.bok = true := by decide +kernel
theorem PrimData39.q15 : PrimData39.s15.bok = true := by decide +kernel
theorem PrimData39.q16 : PrimData39.s16.bok = true := by decide +kernel
theorem PrimData39.q17 : PrimData39.s17.bok = true := by decide +kernel
theorem PrimData39.q18 : PrimData39.s18.bok = true := by decide +kernel
theorem PrimData39.q19 : PrimData39.s19.bok = true := by decide +kernel
theorem PrimData39.q20 : PrimData39.s20.bok = true := by decide +kernel
theorem PrimData39.q21 : PrimData39.s21.bok = true := by decide +kernel
theorem PrimData39.q22 : PrimData39.s22.bok = true := by decide +kernel
theorem PrimData39.q23 : PrimData39.s23.bok = true := by decide +kernel
theorem PrimData39.q24 : PrimData39.s24.bok = true := by decide +kernel
theorem PrimData39.q25 : PrimData39.s25.bok = true := by decide +kernel
theorem PrimData39.q26 : PrimData39.s26.bok = true := by decide +kernel
theorem PrimData39.q27 : PrimData39.s27.bok = true := by decide +kernel
theorem PrimData39.q28 : PrimData39.s28.bok = true := by decide +kernel
theorem PrimData39.q29 : PrimData39.s29.bok = true := by decide +kernel
theorem PrimData39.q30 : PrimData39.s30.bok = true := by decide +kernel
theorem PrimData39.q31 : PrimData39.s31.bok = true := by decide +kernel
theorem PrimData39.q32 : PrimData39.s32.bok = true := by decide +kernel
theorem PrimData39.q33 : PrimData39.s33.bok = true := by decide +kernel
theorem PrimData39.q34 : PrimData39.s34.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData39.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData39.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData39.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData39.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q6, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q7, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q8, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q9, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q10, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q11, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q12, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q13, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q14, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q15, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q16, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q17, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q18, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q19, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q20, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q21, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q22, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q23, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q24, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q25, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q26, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q27, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q28, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q29, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q30, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q31, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q32, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q33, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData39.q34, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
