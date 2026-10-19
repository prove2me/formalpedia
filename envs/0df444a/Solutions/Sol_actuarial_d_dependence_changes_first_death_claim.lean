-- Prove2me | solution 1 for actuarial_d_dependence_changes_first_death_claim
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:53:57.405956+00:00
-- url     : https://prove2.me/submissions/54bd5a6b-7d91-4ad1-b33c-8df756fdddbe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_perfectPairLaw
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem solution  : assureFirst 1 perfectPairLaw (fun _ => 1) ≠ assureFirst 1 productPairLaw (fun _ => 1) := by
  simp [ActuarialJointD.assureFirst, ActuarialJointD.expect, ActuarialJointD.firstPath, ActuarialJointD.perfectPairLaw, ActuarialJointD.productPairLaw, Finset.sum_range_succ]; norm_num
