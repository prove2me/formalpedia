-- Prove2me | solution 1 for SoficGroups.mem_finiteElementaryGenerators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/37909ff3-cd5a-48b2-bb44-439169b76827

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
variable {R : Type*} [Ring R]
namespace SoficGroups
theorem _root_.solution [DecidableEq R] (n : ℕ) (s : Finset R)
    (z : (Matrix (Fin n) (Fin n) R)ˣ) :
    z ∈ finiteElementaryGenerators n s ↔
      ∃ (i j : Fin n) (h : i ≠ j) (a : R),
        a ∈ insert 1 s ∧ elementaryUnit i j h a = z := by
  constructor
  · intro hz
    unfold finiteElementaryGenerators at hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    by_cases h : i ≠ j
    · rw [dif_pos h] at hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, j, h, a, ha, rfl⟩
    · rw [dif_neg h] at hj
      simp at hj
  · rintro ⟨i, j, h, a, ha, rfl⟩
    unfold finiteElementaryGenerators
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [dif_pos h]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
end SoficGroups
