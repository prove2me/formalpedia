-- Prove2me | solution 1 for ValueAwareRR.normalizedResidualMax_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:13:12.065052+00:00
-- url     : https://prove2.me/submissions/4d205ac1-27cf-4339-96d3-0113dc7b5c0a

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_familyA_pos
import Theorems.Thm_ValueAwareRR_residualMax_eq_familyA
import Theorems.Thm_ValueAwareRR_normalizedResidualMax_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    normalizedResidualMax m = 1 := by
  rw [normalizedResidualMax_scaling m hm, residualMax_eq_familyA m hm,
    normalizationScale]
  exact one_div_mul_cancel (ne_of_gt (familyA_pos m hm))
end ValueAwareRR
