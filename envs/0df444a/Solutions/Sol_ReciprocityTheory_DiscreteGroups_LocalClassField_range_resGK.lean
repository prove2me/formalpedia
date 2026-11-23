-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.range_resGK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:44.065322+00:00
-- url     : https://prove2.me/submissions/3f01335a-b0ea-4171-afba-a7767fafcd4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) : (resGK h).range = subG p K L := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    exact ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
