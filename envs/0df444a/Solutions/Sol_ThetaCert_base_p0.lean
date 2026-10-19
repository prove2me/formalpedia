-- Prove2me | solution 1 for ThetaCert.base_p0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:52:32.117672+00:00
-- url     : https://prove2.me/submissions/659c1af7-3140-4f3c-a9c2-fad4df89649e

import Definitions.Def_ThetaCertData_base

namespace ThetaSieve
set_option maxHeartbeats 0

theorem ThetaBase.q0 : ThetaBase.s0.bok = true := by decide +kernel
theorem ThetaBase.q1 : ThetaBase.s1.bok = true := by decide +kernel
theorem ThetaBase.q2 : ThetaBase.s2.bok = true := by decide +kernel
theorem ThetaBase.q3 : ThetaBase.s3.bok = true := by decide +kernel
theorem ThetaBase.q4 : ThetaBase.s4.bok = true := by decide +kernel
theorem ThetaBase.q5 : ThetaBase.s5.bok = true := by decide +kernel
theorem ThetaBase.q6 : ThetaBase.s6.bok = true := by decide +kernel

end ThetaSieve

theorem solution :
    ∀ s ∈ [ThetaSieve.ThetaBase.s0, ThetaSieve.ThetaBase.s1, ThetaSieve.ThetaBase.s2, ThetaSieve.ThetaBase.s3, ThetaSieve.ThetaBase.s4, ThetaSieve.ThetaBase.s5, ThetaSieve.ThetaBase.s6], s.bok = true :=
  List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q0, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q1, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q2, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q3, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q4, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q5, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q6, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩
