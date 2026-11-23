-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.map_divHom_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:41.549896+00:00
-- url     : https://prove2.me/submissions/09730b4b-8675-450a-92a9-73a6bc7a365d

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
theorem _root_.solution {e : ℕ} (he : 0 < e) :
    (AddSubgroup.zmultiples (e : ℤ)).map (divHom e) = AddSubgroup.zmultiples (1 : ℝ) := by
  have he' : (e : ℝ) ≠ 0 := by positivity
  rw [AddMonoidHom.map_zmultiples, divHom_apply]
  congr 1
  rw [Int.cast_natCast, mul_inv_cancel₀ he']
end ReciprocityTheory.DiscreteGroups.LocalClassField
