-- Prove2me | solution 1 for UlmsTheorem.markedGradedInvariant_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:59.677163+00:00
-- url     : https://prove2.me/submissions/114c9e22-3f7a-4237-82d5-ee5b875f1e6a

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) :
    markedGradedInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by
  have hden :
      markedGradedSubmodule p (⊥ : AddSubgroup G) α = ulmDenSubmodule p α := by
    ext x
    simp [markedGradedSubmodule, markedGradedDen, ulmDenSubmodule,
      pSocleAtSuccSubgroupOf]
  unfold markedGradedInvariant ulmInvariant
  change Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ markedGradedSubmodule p (⊥ : AddSubgroup G) α) =
    Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α)
  rw [hden]
end UlmsTheorem
