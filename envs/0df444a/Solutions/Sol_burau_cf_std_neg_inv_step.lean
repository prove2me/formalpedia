-- Prove2me | solution 1 for burau_cf_std_neg_inv_step
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:03:31.712398+00:00
-- url     : https://prove2.me/submissions/6374074c-a959-4094-8b55-2d362991deeb

import Definitions.Def_burau_std_cf
import Theorems.Thm_burau_cf_ediv_neg_of_pos
import Theorems.Thm_burau_cf_emod_neg_of_pos

set_option autoImplicit false

/-- **Uniform recursion of the negative-reciprocal rule**: for all `a, b > 0` the standard Euclidean
descent of the pair `(b, -a)` takes one explicit step. -/
theorem solution (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    cfStd b (-a) = -((a + b - 1) / b) :: cfStd (b * ((a + b - 1) / b) - a) b := by
  rw [cfStd_cons b (-a) (ne_of_gt hb), burau_cf_ediv_neg_of_pos a b ha hb,
    burau_cf_emod_neg_of_pos a b ha hb]
