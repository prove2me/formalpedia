-- Prove2me | solution 1 for actuarial_c_frac_udd_halfyear_ge_cf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:02:34.896394+00:00
-- url     : https://prove2.me/submissions/53bc6273-5554-4415-93c5-06ff9c7e923c

import Mathlib
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_uddHalf
import Definitions.Def_actuarial_c_frac_cfHalf

open ActuarialAssurances.Fractional



theorem solution (p : ℝ) (hp : 0 ≤ p) :
    cfHalf p ≤ uddHalf p := by
  unfold cfHalf uddHalf; nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p, sq_nonneg (Real.sqrt p - 1)]

