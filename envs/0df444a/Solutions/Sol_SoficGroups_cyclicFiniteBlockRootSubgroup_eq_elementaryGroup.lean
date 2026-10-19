-- Prove2me | solution 1 for SoficGroups.cyclicFiniteBlockRootSubgroup_eq_elementaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/93cdf6dd-d8c5-47a5-87ab-a655fd0e1a98

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_one_mem_finiteBlockCoefficientSpan
import Theorems.Thm_SoficGroups_mem_finiteBlockCoefficientSpan_of_mem
import Theorems.Thm_SoficGroups_cyclicFiniteBlockRootSubgroup_le_elementaryGroup
import Theorems.Thm_SoficGroups_elementaryUnit_mem_cyclicFiniteBlockRootSubgroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (s : Finset R)
    (hs : Algebra.adjoin (ZMod 2) (↑s : Set R) = ⊤) :
    cyclicFiniteBlockRootSubgroup (finiteBlockCoefficientSpan s) =
      elementaryGroup (Fin 9) R := by
  let W : Submodule (ZMod 2) R := finiteBlockCoefficientSpan s
  let H : Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
    cyclicFiniteBlockRootSubgroup W
  have hW : (1 : R) ∈ W := one_mem_finiteBlockCoefficientSpan s
  have hunit : ∀ (i j : Fin 9) (hij : i ≠ j),
      elementaryUnit i j hij (1 : R) ∈ H := by
    intro i j hij
    exact elementaryUnit_mem_cyclicFiniteBlockRootSubgroup
      W hW i j hij 1 hW
  let C : Subalgebra (ZMod 2) R :=
    elementaryCoefficientSubalgebra 9 (by decide) H hunit
  have hgen : (↑s : Set R) ⊆ (C : Set R) := by
    intro a ha
    change ∀ (i j : Fin 9) (hij : i ≠ j),
      elementaryUnit i j hij a ∈ H
    intro i j hij
    exact elementaryUnit_mem_cyclicFiniteBlockRootSubgroup
      W hW i j hij a
      (mem_finiteBlockCoefficientSpan_of_mem s ha)
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le hgen
  change H = elementaryGroup (Fin 9) R
  apply le_antisymm
  · exact cyclicFiniteBlockRootSubgroup_le_elementaryGroup W
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    have ha : a ∈ C := by simp [hC]
    exact ha i j hij
end SoficGroups
