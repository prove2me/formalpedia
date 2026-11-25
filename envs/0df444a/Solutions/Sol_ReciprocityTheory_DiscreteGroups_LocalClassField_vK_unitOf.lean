-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.vK_unitOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:42.480807+00:00
-- url     : https://prove2.me/submissions/f0805a3e-69e0-45c2-9f87-d0573824c4ce

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vOn_spec


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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (x : multOf p K) : vK p K (unitOf p K x) = vOn p K x := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, vOn_spec, vbar_apply]
  show - ((eK p K : ℝ) * Real.logb p ‖((Additive.toMul x.1 : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖) = _
  ring
end ReciprocityTheory.DiscreteGroups.LocalClassField
