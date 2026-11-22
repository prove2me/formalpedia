-- Prove2me | solution 1 for UlmsTheorem.kaplansky_room_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:49.075455+00:00
-- url     : https://prove2.me/submissions/cb2fbefb-4f34-4b8b-a90f-fa9ea5eec726

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
    kaplanskyRoomInvariant p S α U +
        Module.rank (ZMod p) (kaplanskyOccupiedSubmodule p S α U) =
      ulmInvariant p α (G := G) := by
  exact Submodule.rank_quotient_add_rank (kaplanskyOccupiedSubmodule p S α U)
end UlmsTheorem
