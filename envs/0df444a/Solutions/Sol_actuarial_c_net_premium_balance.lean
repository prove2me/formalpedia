-- Prove2me | solution 1 for actuarial_c_net_premium_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:03:40.230471+00:00
-- url     : https://prove2.me/submissions/c1f64b92-6ad4-4928-84de-8595b9500d72

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_netPremium

open ActuarialAssurances



theorem solution (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : 0 < due h n v p) : netPremium h n v b p*due h n v p=term h n v b p := by
  unfold netPremium; field_simp [ha.ne']

