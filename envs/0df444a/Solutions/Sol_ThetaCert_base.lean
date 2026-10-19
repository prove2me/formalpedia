-- Prove2me | solution 1 for ThetaCert.base
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:52:31.300977+00:00
-- url     : https://prove2.me/submissions/66f318ff-ab26-481e-9e8a-f781d8c56783

import Theorems.Thm_ThetaCert_base_p0
import Theorems.Thm_ThetaCert_base_p1
import Theorems.Thm_ThetaCert_base_p2
import Theorems.Thm_ThetaCert_base_p3

theorem solution :
    ∀ s ∈ ThetaSieve.ThetaBase.segs, s.bok = true := by
  show ∀ s ∈ [ThetaSieve.ThetaBase.s0, ThetaSieve.ThetaBase.s1, ThetaSieve.ThetaBase.s2, ThetaSieve.ThetaBase.s3, ThetaSieve.ThetaBase.s4, ThetaSieve.ThetaBase.s5, ThetaSieve.ThetaBase.s6] ++ ([ThetaSieve.ThetaBase.s7, ThetaSieve.ThetaBase.s8, ThetaSieve.ThetaBase.s9, ThetaSieve.ThetaBase.s10, ThetaSieve.ThetaBase.s11, ThetaSieve.ThetaBase.s12, ThetaSieve.ThetaBase.s13] ++ ([ThetaSieve.ThetaBase.s14, ThetaSieve.ThetaBase.s15, ThetaSieve.ThetaBase.s16, ThetaSieve.ThetaBase.s17, ThetaSieve.ThetaBase.s18, ThetaSieve.ThetaBase.s19, ThetaSieve.ThetaBase.s20] ++ ([ThetaSieve.ThetaBase.s21, ThetaSieve.ThetaBase.s22, ThetaSieve.ThetaBase.s23, ThetaSieve.ThetaBase.s24, ThetaSieve.ThetaBase.s25, ThetaSieve.ThetaBase.s26, ThetaSieve.ThetaBase.s27]))), s.bok = true
  exact List.forall_mem_append.2 ⟨ThetaCert.base_p0, List.forall_mem_append.2 ⟨ThetaCert.base_p1, List.forall_mem_append.2 ⟨ThetaCert.base_p2, ThetaCert.base_p3⟩⟩⟩
