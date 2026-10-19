-- Prove2me | solution 1 for ThetaCert.base_p1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:52:32.691973+00:00
-- url     : https://prove2.me/submissions/3de563f9-157f-4086-be9b-04263b4cbdb4

import Definitions.Def_ThetaCertData_base

namespace ThetaSieve
set_option maxHeartbeats 0

theorem ThetaBase.q7 : ThetaBase.s7.bok = true := by decide +kernel
theorem ThetaBase.q8 : ThetaBase.s8.bok = true := by decide +kernel
theorem ThetaBase.q9 : ThetaBase.s9.bok = true := by decide +kernel
theorem ThetaBase.q10 : ThetaBase.s10.bok = true := by decide +kernel
theorem ThetaBase.q11 : ThetaBase.s11.bok = true := by decide +kernel
theorem ThetaBase.q12 : ThetaBase.s12.bok = true := by decide +kernel
theorem ThetaBase.q13 : ThetaBase.s13.bok = true := by decide +kernel

end ThetaSieve

theorem solution :
    ∀ s ∈ [ThetaSieve.ThetaBase.s7, ThetaSieve.ThetaBase.s8, ThetaSieve.ThetaBase.s9, ThetaSieve.ThetaBase.s10, ThetaSieve.ThetaBase.s11, ThetaSieve.ThetaBase.s12, ThetaSieve.ThetaBase.s13], s.bok = true :=
  List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q7, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q8, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q9, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q10, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q11, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q12, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q13, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩
