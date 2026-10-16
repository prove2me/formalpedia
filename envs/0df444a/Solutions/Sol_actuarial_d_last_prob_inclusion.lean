-- Prove2me | solution 1 for actuarial_d_last_prob_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:47:11.904141+00:00
-- url     : https://prove2.me/submissions/fbdc11ef-1218-43d6-82e2-5690d8276929

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_plast
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_expect
import Theorems.Thm_actuarial_d_last_inclusion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h t : ℕ) (p : ℕ → ℕ → ℝ) :
    plast h p t = px h p t + py h p t - pxy h p t := by
  unfold plast px py pxy expect
  simp_rw [actuarial_d_last_inclusion]
  simp_rw [mul_sub, mul_add]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
