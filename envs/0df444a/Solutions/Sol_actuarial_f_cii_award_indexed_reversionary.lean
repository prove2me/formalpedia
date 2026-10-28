-- Prove2me | solution 1 for actuarial_f_cii_award_indexed_reversionary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:06:40.734708+00:00
-- url     : https://prove2.me/submissions/a56703ca-dd35-42ad-82f5-1b2cc0cc06dc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Theorems.Thm_actuarial_d_reversionary_annuity

open ActuarialUnderpinsF



theorem solution
    (awards horizon payments : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc : ℕ → ℝ)
    (benefit : ℕ → ℕ → ℝ) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j =>
        ActuarialJointD.annPath payments disc (benefit z)
          (ActuarialJointD.onlyY i j)) =
      ∑ z ∈ Finset.range awards,
        (ActuarialJointD.annY horizon payments
          (fun i j => p z i j) disc (benefit z) -
         ActuarialJointD.annJoint horizon payments
          (fun i j => p z i j) disc (benefit z)) := by
  unfold ActuarialUnderpinsF.expect
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold ActuarialJointD.annY ActuarialJointD.annJoint ActuarialJointD.annValue
    ActuarialJointD.expect
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ActuarialJointD.annPath
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  beta_reduce
  simp only [ActuarialJointD.onlyY, ActuarialJointD.dead, ActuarialJointD.both]
  ring
