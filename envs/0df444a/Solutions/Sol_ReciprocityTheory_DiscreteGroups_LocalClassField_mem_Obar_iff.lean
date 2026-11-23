-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:27.181965+00:00
-- url     : https://prove2.me/submissions/dd1f3a2f-4b11-4d45-8ced-cdd4715ead64

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {x : PadicAlgCl p} : x ∈ Obar p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
