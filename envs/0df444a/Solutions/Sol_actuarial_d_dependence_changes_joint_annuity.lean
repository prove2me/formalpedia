-- Prove2me | solution 1 for actuarial_d_dependence_changes_joint_annuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:09:03.50281+00:00
-- url     : https://prove2.me/submissions/80d5f506-7fad-41b6-adc6-724ce9c2c727

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_d_both
import Definitions.Def_actuarial_d_annJoint
import Definitions.Def_actuarial_d_perfectPairLaw
import Definitions.Def_actuarial_d_productPairLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialJointD

theorem solution  : annJoint 1 2 perfectPairLaw (fun _ => 1) (fun _ => 1) ≠ annJoint 1 2 productPairLaw (fun _ => 1) (fun _ => 1) := by
  norm_num [annJoint, annValue, annPath, expect,
    perfectPairLaw, productPairLaw, both, alive,
    Finset.sum_range_succ]
