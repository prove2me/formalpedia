-- Prove2me | solution 1 for actuarial_f_post88_gmp_no_october_april_uplift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:53:01.899562+00:00
-- url     : https://prove2.me/submissions/5cc367cc-090f-41de-9898-702b807e8650

import Mathlib
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease
open ActuarialUnderpinsF

theorem solution :
    gmpPost88AprilIncrease 20261001 20270405
      (fun _ => (7 / 100 : ℝ)) 2027 = 0 := by
  norm_num [gmpPost88AprilIncrease, gmpStatutoryAprilEligible, gmpSixApril]
