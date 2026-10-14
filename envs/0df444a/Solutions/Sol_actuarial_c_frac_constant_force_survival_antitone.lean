-- Prove2me | solution 1 for actuarial_c_frac_constant_force_survival_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:21:45.237173+00:00
-- url     : https://prove2.me/submissions/5cab7758-e8ff-41fc-bb10-0957a8f63437

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_cfSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Fractional

theorem solution (p u v : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (huv : u ≤ v) :
    cfSurvival p v ≤ cfSurvival p u := by
  have hlog : Real.log p ≤ 0 := by
    have h := Real.log_le_log hp hp1
    simpa using h
  unfold cfSurvival
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left huv hlog)
