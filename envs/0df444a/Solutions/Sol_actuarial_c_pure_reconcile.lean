-- Prove2me | solution 1 for actuarial_c_pure_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:17:12.27512+00:00
-- url     : https://prove2.me/submissions/2e959de3-7882-4cb0-820f-8dfea1166b90

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure
import Definitions.Def_actuarial_c_pureMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances

theorem solution (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) :
    pure h n v p = pureMass h n v p := by
  unfold ActuarialAssurances.pure pureMass surv purePath
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
