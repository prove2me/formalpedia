-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IndexUBound.prod_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:57.525879+00:00
-- url     : https://prove2.me/submissions/65689c33-46e5-42c7-a2d9-b63f70c5c678

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexUpperBound_OneSubSumLeProd
import Theorems.Thm_PI_UnitaryGroupMassFormula_IndexUBound_prod_Ico_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IndexUBound
open Finset
namespace PI.UnitaryGroupMassFormula.IndexUBound
theorem _root_.solution (g : ℝ) (hg : g ≠ 0) (r : ℕ) :
    ∏ i ∈ Ico 1 r, (g ^ i - 1) = g ^ (r * (r - 1) / 2) * ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) := by
  rw [← PI.UnitaryGroupMassFormula.IndexUBound.prod_Ico_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_sub, mul_one, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hg)]
end PI.UnitaryGroupMassFormula.IndexUBound
