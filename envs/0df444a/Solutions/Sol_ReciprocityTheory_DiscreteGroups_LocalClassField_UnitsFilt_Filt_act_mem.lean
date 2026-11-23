-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.act_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:47.559851+00:00
-- url     : https://prove2.me/submissions/bc4a82bb-991c-4f3a-a7b5-4361d0e12396

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_act_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Filt_mem_V


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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)
include h
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
theorem _root_.solution {n : ℕ} (g : G) {u : Rˣ} (hu : u ∈ h.V n) : act g u ∈ h.V n := by
  rw [mem_V, act_val]
  have := h.smul n g _ hu
  rwa [smul_sub, smul_one] at this
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
