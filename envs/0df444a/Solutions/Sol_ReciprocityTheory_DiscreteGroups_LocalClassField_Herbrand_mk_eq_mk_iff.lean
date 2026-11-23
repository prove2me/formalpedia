-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:47.482809+00:00
-- url     : https://prove2.me/submissions/30d77d13-26bf-4de5-bd59-eabf8225924c

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {M : Type*} [AddCommGroup M]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution {D N : M →+ M} (x y : D.ker) :
    (QuotientAddGroup.mk x : T D N) = QuotientAddGroup.mk y ↔ (x : M) - y ∈ N.range := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]; rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
