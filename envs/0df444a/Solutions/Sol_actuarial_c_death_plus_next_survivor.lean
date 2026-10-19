-- Prove2me | solution 1 for actuarial_c_death_plus_next_survivor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:53:04.381001+00:00
-- url     : https://prove2.me/submissions/4f6cf6bf-5082-4087-8003-c96bd0156af7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death

open ActuarialAssurances


theorem solution (k j : ℕ) :
    alive k j = death k j + alive k (j+1) := by
  intros; simp [ActuarialAssurances.alive, ActuarialAssurances.death]; split_ifs <;> simp_all <;> omega

