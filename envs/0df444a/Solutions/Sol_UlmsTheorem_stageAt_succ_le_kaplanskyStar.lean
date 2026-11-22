-- Prove2me | solution 1 for UlmsTheorem.stageAt_succ_le_kaplanskyStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:46.163608+00:00
-- url     : https://prove2.me/submissions/dc5fcb23-3f95-40de-80d5-812db862b35d

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_succ


set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp
namespace UlmsTheorem
theorem _root_.solution (S : AddSubgroup G) (α : Ordinal) :
    stageAt p S (Order.succ α) ≤ kaplanskyStar p S α := by
  intro x hx
  have hxS : x ∈ S := hx.1
  have hxα1 : x ∈ ulmSubgroup p (Order.succ α) := hx.2
  have hxα : x ∈ ulmSubgroup p α :=
    ulmSubgroup_antitone p (Order.le_succ α) hxα1
  refine ⟨hxS, hxα, ?_⟩
  rw [ulmSubgroup_succ]
  exact ⟨x, hxα1, rfl⟩
end UlmsTheorem
