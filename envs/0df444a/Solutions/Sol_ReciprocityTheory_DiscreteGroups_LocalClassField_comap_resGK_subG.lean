-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.comap_resGK_subG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:00.931027+00:00
-- url     : https://prove2.me/submissions/5c38584f-9ecd-4e15-92a8-696c908ae5c1

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
theorem _root_.solution (h : K ≤ L) (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (subG p K L').comap (resGK h) = subG p L L' := by
  ext σ
  exact Iff.rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
