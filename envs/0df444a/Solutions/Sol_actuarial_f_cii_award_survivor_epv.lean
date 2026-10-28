-- Prove2me | solution 1 for actuarial_f_cii_award_survivor_epv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:07:16.11247+00:00
-- url     : https://prove2.me/submissions/1c82ab33-185f-453c-a656-d7f7a99f3f3e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint

open ActuarialUnderpinsF



theorem solution
    (awards horizon payments : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc : ℕ → ℝ)
    (benefit : ℕ → ℕ → ℝ) (hpayments : payments ≤ horizon + 1) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j =>
        ActuarialJointD.annPath payments disc (benefit z)
          (fun t => ActuarialUnderpinsF.spouseDue horizon i j t)) =
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
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  have hs : spouseDue horizon i j t = ActuarialJointD.onlyY i j t := by
    unfold spouseDue
    split_ifs with hi
    · rfl
    · simp [ActuarialJointD.onlyY, ActuarialJointD.dead, ActuarialJointD.alive,
        show t ≤ i by omega]
  beta_reduce
  rw [hs]
  simp only [ActuarialJointD.onlyY, ActuarialJointD.dead, ActuarialJointD.both]
  ring
