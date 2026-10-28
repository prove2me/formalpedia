-- Prove2me | solution 1 for actuarial_f_cii_award_guarantee_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:04:45.345761+00:00
-- url     : https://prove2.me/submissions/190f14c2-886d-484f-8ffb-1e431d30c56b

import Mathlib
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_d_guaranteeParallelPath
import Definitions.Def_actuarial_d_guaranteeParallelValue
import Definitions.Def_actuarial_d_guaranteeDelayValue
import Definitions.Def_actuarial_d_guaranteeOverlapValue
import Theorems.Thm_actuarial_d_guarantee_value_difference
open ActuarialUnderpinsF

theorem solution
    (awards horizon payments guaranteed : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc benefit : ℕ → ℝ) (rho : ℝ) :
    ActuarialUnderpinsF.expect awards horizon p
      (fun z i j =>
        ActuarialJointD.guaranteeParallelPath payments guaranteed
          disc benefit rho i j) =
      ∑ z ∈ Finset.range awards,
        (ActuarialJointD.guaranteeDelayValue horizon payments guaranteed
          (fun i j => p z i j) disc benefit rho +
         rho * ActuarialJointD.guaranteeOverlapValue horizon payments guaranteed
          (fun i j => p z i j) disc benefit) := by
  unfold ActuarialUnderpinsF.expect
  refine Finset.sum_congr rfl fun z _ => ?_
  exact actuarial_d_guarantee_value_difference horizon payments guaranteed (fun i j => p z i j) disc benefit rho
