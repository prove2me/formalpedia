-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.sum_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:58:43.774112+00:00
-- url     : https://prove2.me/submissions/378d49f4-7c9d-4d83-9652-97bbd2a57fa3

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
theorem _root_.solution {g₀ : G} (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (f : G → R) :
    ∑ k ∈ range (orderOf g₀), f (g₀ ^ k) = ∑ g, f g := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, sum_image]
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
