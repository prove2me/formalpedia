-- Prove2me | solution 1 for actuarial_d_pure_last_decomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:04:59.133442+00:00
-- url     : https://prove2.me/submissions/e8e3b74f-ee48-4f32-a8c5-e6855fc8dac0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_d_pureLast
import Definitions.Def_actuarial_d_pureX
import Definitions.Def_actuarial_d_pureY
import Definitions.Def_actuarial_d_pureJoint
import Definitions.Def_actuarial_d_plast
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Theorems.Thm_actuarial_d_last_prob_inclusion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h t : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    pureLast h t p d = pureX h t p d + pureY h t p d - pureJoint h t p d := by
  unfold pureLast pureX pureY pureJoint
  rw [actuarial_d_last_prob_inclusion]
  ring
