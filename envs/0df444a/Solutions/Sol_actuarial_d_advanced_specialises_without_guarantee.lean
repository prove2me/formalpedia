-- Prove2me | solution 1 for actuarial_d_advanced_specialises_without_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T14:56:51.692881+00:00
-- url     : https://prove2.me/submissions/1c6e6da2-e31a-41b8-af15-98ee1291d5f1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_advancedPath
import Definitions.Def_actuarial_d_totalPath
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_guaranteeMember
import Definitions.Def_actuarial_d_delayedSpouse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : advancedValue h 0 n 0 p d b rho f s fx fy ft = totalValue h n p d b rho f s fx fy ft := by
  simp [advancedValue, totalValue, advancedPath, totalPath,
    annRange, annPath, guaranteeMember, delayedSpouse]
