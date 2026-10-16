-- Prove2me | solution 1 for actuarial_c_endow_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:18:17.053975+00:00
-- url     : https://prove2.me/submissions/06b477b8-9580-4ad2-92e9-15a1c0abdeff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances

theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    endow h n v b p = term h n v b p + pure h n v p := by
  unfold endow endowPath term ActuarialAssurances.pure
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring
