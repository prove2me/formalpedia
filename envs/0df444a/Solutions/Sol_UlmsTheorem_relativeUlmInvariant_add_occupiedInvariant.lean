-- Prove2me | solution 1 for UlmsTheorem.relativeUlmInvariant_add_occupiedInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:07.261202+00:00
-- url     : https://prove2.me/submissions/73381fc6-1ce8-4e08-ac5d-8e547f3a4954

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant p S α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p S α) =
      ulmInvariant p α (G := G) := by
  unfold relativeUlmInvariant hillInvariant ulmInvariant
  rw [← (occupiedQuotientEquivRelative p S α).rank_eq]
  exact Submodule.rank_quotient_add_rank (relativeOccupiedSubmodule p S α)
end UlmsTheorem
