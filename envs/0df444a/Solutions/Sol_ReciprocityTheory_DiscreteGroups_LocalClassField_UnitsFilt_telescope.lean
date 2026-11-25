-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.telescope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:58:56.308601+00:00
-- url     : https://prove2.me/submissions/8c5386e4-3c7b-421f-adf2-459e9b582e5f

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
theorem _root_.solution (g₀ : G) (z : R) (k : ℕ) :
    g₀ • ∑ j ∈ range k, g₀ ^ j • z - ∑ j ∈ range k, g₀ ^ j • z = g₀ ^ k • z - z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, smul_add, smul_smul, ← pow_succ']
    linear_combination ih
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
