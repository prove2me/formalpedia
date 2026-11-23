-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.V_sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:31.409816+00:00
-- url     : https://prove2.me/submissions/33fdfc41-a42d-4f2e-8be3-6f41ef958bc3

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA

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
variable {R : Type*} [Field R] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G R]
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
variable {G} {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
theorem _root_.solution (u : Rˣ) (hu : ∀ n, u ∈ h.V n) : u = 1 :=
  Units.ext (sub_eq_zero.1 (h.sep _ hu))
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
