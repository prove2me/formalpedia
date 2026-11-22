-- Prove2me | solution 1 for UlmsTheorem.kaplansky_not_surjective_iff_room
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:09.760647+00:00
-- url     : https://prove2.me/submissions/45f3a408-1d30-42bc-8599-209d1de9951b

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

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    ¬ Function.Surjective U ↔ Nontrivial (kaplanskyRoomQuotient p S α U) := by
  rw [Submodule.Quotient.nontrivial_iff]
  change (¬ Function.Surjective U) ↔
    LinearMap.range (kaplanskyLinearMap p S α U) ≠ ⊤
  rw [ne_eq, LinearMap.range_eq_top]
  rfl
end UlmsTheorem
