-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_le_iff_of_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:00.716072+00:00
-- url     : https://prove2.me/submissions/3412ce8a-1dc5-4b4a-a46c-d2ae7462a8ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_lt_of_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_le_of_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} [Fact l.Prime] (r : PadicAlgCl l →+* PadicAlgCl l)
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) (z : PadicAlgCl l) : ‖r z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  refine ⟨fun h => ?_, fun h => norm_le_of_res hr h⟩
  by_contra hz
  push Not at hz
  have h1 : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have h2 := norm_lt_of_res hr h1
  rw [map_inv₀, norm_inv] at h2
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    linarith
  have h3 : 0 < ‖r z‖ := norm_pos_iff.2 ((map_ne_zero r).2 hz0)
  have h4 : 1 ≤ ‖r z‖⁻¹ := (one_le_inv₀ h3).2 h
  linarith
end ReciprocityTheory.ChartRestriction.L1
