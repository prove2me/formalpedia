-- Prove2me | solution 1 for actuarial_d_same_margins_different_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:05:33.300678+00:00
-- url     : https://prove2.me/submissions/70c362ca-8a0d-46f7-b085-421319f710d7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_perfectPairLaw
import Definitions.Def_actuarial_d_productPairLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution  : px 1 perfectPairLaw 1 = px 1 productPairLaw 1 ∧ py 1 perfectPairLaw 1 = py 1 productPairLaw 1 ∧ pxy 1 perfectPairLaw 1 ≠ pxy 1 productPairLaw 1 := by
  norm_num [px, py, pxy, expect, perfectPairLaw, productPairLaw,
    both, alive, Finset.sum_range_succ]
