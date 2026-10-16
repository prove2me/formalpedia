-- Prove2me | solution 1 for actuarial_d_marginal_joint_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:07:04.215433+00:00
-- url     : https://prove2.me/submissions/a4de6bb8-b4d9-4839-a289-a411e05d1678

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_both
import Theorems.Thm_actuarial_d_alive_zero
import Theorems.Thm_actuarial_d_law_total_expected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution (h : ℕ) (p : ℕ → ℕ → ℝ) (hp : valid h p) :
    px h p 0 = 1 ∧ py h p 0 = 1 ∧ pxy h p 0 = 1 := by
  have hm : expect h p (fun _ _ => (1 : ℝ)) = 1 :=
    actuarial_d_law_total_expected h p hp
  refine ⟨?_, ?_, ?_⟩
  · unfold px
    simpa only [actuarial_d_alive_zero] using hm
  · unfold py
    simpa only [actuarial_d_alive_zero] using hm
  · unfold pxy both
    simpa only [actuarial_d_alive_zero, one_mul] using hm
