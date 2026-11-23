-- Prove2me | solution 1 for PI.GTNum.prod_pow_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:46.842626+00:00
-- url     : https://prove2.me/submissions/da163c37-90b6-416f-bb84-3f985d735010

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GTNum
open Finset
namespace PI.GTNum
theorem _root_.solution {α : Type*} (s : Finset α) (B : ℤ) (m : ℕ) (e : α → ℕ) :
    ∏ x ∈ s, (B ^ m) ^ e x = B ^ (m * ∑ x ∈ s, e x) := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
end PI.GTNum
