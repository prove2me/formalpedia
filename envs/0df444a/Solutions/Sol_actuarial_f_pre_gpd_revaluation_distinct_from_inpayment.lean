-- Prove2me | solution 1 for actuarial_f_pre_gpd_revaluation_distinct_from_inpayment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:02:26.029353+00:00
-- url     : https://prove2.me/submissions/84182fc3-b341-4e8a-9a0e-aa22646aae89

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpRevaluedAtPayable

open ActuarialUnderpinsF



theorem solution
    (pre88 post88 preFactor postFactor : ℝ) :
    gmpRevaluedAtPayable pre88 post88 preFactor postFactor =
      pre88 * preFactor + post88 * postFactor := by
  rfl
