-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.divHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:41.415607+00:00
-- url     : https://prove2.me/submissions/c0527d26-5908-4e20-b5ff-a41dd2b03fa2

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_divHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {e : ℕ} (he : 0 < e) : Function.Injective (divHom e) := by
  have he' : (e : ℝ) ≠ 0 := by positivity
  intro a b hab
  rw [divHom_apply, divHom_apply] at hab
  exact_mod_cast mul_right_cancel₀ (inv_ne_zero he') hab
end ReciprocityTheory.DiscreteGroups.LocalClassField
