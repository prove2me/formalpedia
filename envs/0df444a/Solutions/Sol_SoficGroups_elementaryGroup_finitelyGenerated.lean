-- Prove2me | solution 1 for SoficGroups.elementaryGroup_finitelyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/73a76c00-5b83-4d41-b360-d9c68e565ab9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_mem_finiteElementaryGenerators

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
variable {R : Type*} [Ring R]
variable [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ) (hn : 2 < n) :
    Group.FG (elementaryGroup (Fin n) R) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ZMod 2) (A := R)
  let t : Finset (Matrix (Fin n) (Fin n) R)ˣ :=
    finiteElementaryGenerators n s
  let H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
    Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ)
  have hunit : ∀ (i j : Fin n) (h : i ≠ j),
      elementaryUnit i j h (1 : R) ∈ H := by
    intro i j hij
    apply Subgroup.subset_closure
    change elementaryUnit i j hij (1 : R) ∈ finiteElementaryGenerators n s
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, 1, Finset.mem_insert_self 1 s, rfl⟩
  let C : Subalgebra (ZMod 2) R :=
    elementaryCoefficientSubalgebra n hn H hunit
  have hgen : (s : Set R) ⊆ (C : Set R) := by
    intro a ha i j hij
    apply Subgroup.subset_closure
    change elementaryUnit i j hij a ∈ finiteElementaryGenerators n s
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, a, Finset.mem_insert_of_mem ha, rfl⟩
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le hgen
  have heq : H = elementaryGroup (Fin n) R := by
    apply le_antisymm
    · change Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ) ≤ _
      rw [Subgroup.closure_le]
      intro z hz
      change z ∈ finiteElementaryGenerators n s at hz
      obtain ⟨i, j, hij, a, _, rfl⟩ :=
        (mem_finiteElementaryGenerators n s z).mp hz
      exact elementaryUnit_mem i j hij a
    · rw [elementaryGroup, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, a, rfl⟩
      have ha : a ∈ C := by simp [hC]
      exact ha i j hij
  apply (Group.fg_iff_subgroup_fg (elementaryGroup (Fin n) R)).mpr
  exact ⟨t, heq⟩
end SoficGroups
