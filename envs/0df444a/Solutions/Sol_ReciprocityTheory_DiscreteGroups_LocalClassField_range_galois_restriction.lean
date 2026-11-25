-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.range_galois_restriction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:44.497438+00:00
-- url     : https://prove2.me/submissions/f5f98db5-586f-4176-a82f-488aff6dd599

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
    exact ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x.1 x.2 }, rfl⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
