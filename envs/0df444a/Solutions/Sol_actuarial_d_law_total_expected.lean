-- Prove2me | solution 1 for actuarial_d_law_total_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:02:12.338268+00:00
-- url     : https://prove2.me/submissions/cf2231db-d738-48bb-b613-97d054a8c012

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) (hp : valid h p) :
    expect h p (fun _ _ => (1 : ℝ)) = 1 := by
  simpa only [expect, mass, mul_one] using hp.2
