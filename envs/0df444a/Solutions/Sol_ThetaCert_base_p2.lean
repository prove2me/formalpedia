-- Prove2me | solution 1 for ThetaCert.base_p2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:52:33.296433+00:00
-- url     : https://prove2.me/submissions/3a75bbd1-75b9-4678-8817-960c9374953c

import Definitions.Def_ThetaCertData_base

namespace ThetaSieve
set_option maxHeartbeats 0

theorem ThetaBase.q14 : ThetaBase.s14.bok = true := by decide +kernel
theorem ThetaBase.q15 : ThetaBase.s15.bok = true := by decide +kernel
theorem ThetaBase.q16 : ThetaBase.s16.bok = true := by decide +kernel
theorem ThetaBase.q17 : ThetaBase.s17.bok = true := by decide +kernel
theorem ThetaBase.q18 : ThetaBase.s18.bok = true := by decide +kernel
theorem ThetaBase.q19 : ThetaBase.s19.bok = true := by decide +kernel
theorem ThetaBase.q20 : ThetaBase.s20.bok = true := by decide +kernel

end ThetaSieve

theorem solution :
    ∀ s ∈ [ThetaSieve.ThetaBase.s14, ThetaSieve.ThetaBase.s15, ThetaSieve.ThetaBase.s16, ThetaSieve.ThetaBase.s17, ThetaSieve.ThetaBase.s18, ThetaSieve.ThetaBase.s19, ThetaSieve.ThetaBase.s20], s.bok = true :=
  List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q14, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q15, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q16, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q17, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q18, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q19, List.forall_mem_cons.2 ⟨ThetaSieve.ThetaBase.q20, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩
