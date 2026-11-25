-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rmu_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:04.086016+00:00
-- url     : https://prove2.me/submissions/ca782dcb-550f-449b-a3bf-119878ef6ecb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsPowerMulUnitNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_power_mul_unitNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {a : ℂ_[l]} (ha : a ∈ Rmu l) (ha0 : a ≠ 0) :
    ∃ m : ℕ, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖a‖⁻¹) (by exact_mod_cast (Fact.out : l.Prime).one_lt :
    (1 : ℝ) < l)
  refine exists_power_mul_unitNorm l k a ha ha0 ?_
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  calc (1 : ℝ) = ‖a‖⁻¹ * ‖a‖ := (inv_mul_cancel₀ hpos.ne').symm
    _ < (l : ℝ) ^ k * ‖a‖ := mul_lt_mul_of_pos_right hk hpos
end ReciprocityTheory.ChartRestriction.L1
