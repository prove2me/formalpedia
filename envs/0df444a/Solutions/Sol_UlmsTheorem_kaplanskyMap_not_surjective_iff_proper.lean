-- Prove2me | solution 1 for UlmsTheorem.kaplanskyMap_not_surjective_iff_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:17.055891+00:00
-- url     : https://prove2.me/submissions/99c37222-6b55-4672-a6b4-e0daa7986fba

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
public import Theorems.Thm_UlmsTheorem_kaplansky_not_surjective_iff_room
public import Theorems.Thm_UlmsTheorem_kaplanskyMap_range
public import Theorems.Thm_UlmsTheorem_relativeUlmQuotient_nontrivial_iff_proper

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
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    ¬ Function.Surjective (kaplanskyMap p S α) ↔
      ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
        v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
        IsProper p S v := by
  rw [kaplansky_not_surjective_iff_room p S α (kaplanskyMap p S α)]
  rw [Submodule.Quotient.nontrivial_iff]
  change LinearMap.range
      (kaplanskyLinearMap p S α (kaplanskyMap p S α)) ≠ ⊤ ↔ _
  rw [kaplanskyMap_range p S α]
  rw [← Submodule.Quotient.nontrivial_iff]
  have hroom :
      Nontrivial (ulmQuotient p α (G := G) ⧸ relativeOccupiedSubmodule p S α) ↔
        Nontrivial (relativeUlmQuotient p S α) := by
    constructor
    · intro h
      let _ := h
      exact (occupiedQuotientEquivRelative p S α).symm.toEquiv.nontrivial
    · intro h
      let _ := h
      exact (occupiedQuotientEquivRelative p S α).toEquiv.nontrivial
  exact hroom.trans (relativeUlmQuotient_nontrivial_iff_proper p S α)
end UlmsTheorem
