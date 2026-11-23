-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt.prod_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:31.545131+00:00
-- url     : https://prove2.me/submissions/b8e7b557-9fd4-4a40-9ed1-0ccc78f745ba

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
theorem _root_.solution {ι : Type*} {n : ℕ} (s : Finset ι) (y : ι → R) (hy : ∀ j ∈ s, y j ∈ I n) :
    ∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j ∈ I (n + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hE := ih fun j hj => hy j (mem_insert_of_mem hj)
    have hS : ∑ j ∈ s, y j ∈ I n := (I n).sum_mem fun j hj => hy j (mem_insert_of_mem hj)
    have hya := hy a (mem_insert_self a s)
    rw [prod_insert ha, sum_insert ha]
    have : (1 + y a) * ∏ j ∈ s, (1 + y j) - 1 - (y a + ∑ j ∈ s, y j) =
        (∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j) + y a * (∏ j ∈ s, (1 + y j) - 1 - ∑ j ∈ s, y j)
          + y a * ∑ j ∈ s, y j := by ring
    rw [this]
    exact (I (n + 1)).add_mem ((I (n + 1)).add_mem hE (h.mul n _ _ hya (h.le_zero _ hE)))
      (h.mul n _ _ hya (h.le_zero _ hS))
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Filt
