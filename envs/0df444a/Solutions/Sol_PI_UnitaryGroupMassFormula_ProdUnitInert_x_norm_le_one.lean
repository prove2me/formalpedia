-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.x_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:36.381572+00:00
-- url     : https://prove2.me/submissions/1fb4abd9-6379-491d-93cf-96aeb8815cb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_natCast_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution (d : ℕ) (X Y : ℚ_[p]) (hY : ‖Y‖ ≤ 1)
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖X‖ ≤ 1 := by
  have hX2 : X ^ 2 = 1 + (-(d * Y ^ 2)) := by linear_combination h
  have hd1 := natCast_norm_le_one (p := p) d
  have hle : ‖X‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hX2]
    refine (Padic.nonarchimedean _ _).trans (max_le (le_of_eq norm_one) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h0 : ‖Y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Y]
    nlinarith [norm_nonneg (d : ℚ_[p]), norm_nonneg Y, sq_nonneg ‖Y‖]
  nlinarith [norm_nonneg X]
end PI.UnitaryGroupMassFormula.ProdUnitInert
