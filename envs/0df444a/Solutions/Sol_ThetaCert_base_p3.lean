-- Prove2me | solution 1 for ThetaCert.base_p3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:52:34.136976+00:00
-- url     : https://prove2.me/submissions/f9bad607-1db9-44f6-9f6f-c0ebddb1ad1c

import Definitions.Def_ThetaCertData_base

namespace ThetaSieve
set_option maxHeartbeats 0

theorem ThetaBase.q21 : ThetaBase.s21.bok = true := by decide +kernel
theorem ThetaBase.q22 : ThetaBase.s22.bok = true := by decide +kernel
theorem ThetaBase.q23 : ThetaBase.s23.bok = true := by decide +kernel
theorem ThetaBase.q24 : ThetaBase.s24.bok = true := by decide +kernel
theorem ThetaBase.q25 : ThetaBase.s25.bok = true := by decide +kernel
theorem ThetaBase.q26 : ThetaBase.s26.bok = true := by decide +kernel
theorem ThetaBase.q27 : ThetaBase.s27.bok = true := by decide +kernel

end ThetaSieve

theorem solution :
    ∀ s ∈ [ThetaSieve.ThetaBase.s21, ThetaSieve.ThetaBase.s22, ThetaSieve.ThetaBase.s23, ThetaSieve.ThetaBase.s24, ThetaSieve.ThetaBase.s25, ThetaSieve.ThetaBase.s26, ThetaSieve.ThetaBase.s27], s.bok = true :=
  List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q21, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q22, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q23, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q24, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q25, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q26, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q27, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩
