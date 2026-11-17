-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T13:19:37.720202+00:00
-- url     : https://prove2.me/submissions/620d1605-8a31-47ea-9c60-4d5f1fd88adc

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting
import Theorems.Thm_QAOAE3Lin2_General_eq_25

open QAOAE3Lin2.Typical

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (rhs : Fin m → Bool) (i : Fin m) (γ : ℝ) :
    clauseTerm tri rhs i γ = QAOAE3Lin2.General.clauseSin tri rhs i γ := by
  unfold clauseTerm
  exact QAOAE3Lin2.General.eq_25 tri rhs htri i γ
