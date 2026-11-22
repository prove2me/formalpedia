-- Prove2me | solution 1 for UlmsTheorem.relativeUlmInvariant_add_overhangInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:17.541903+00:00
-- url     : https://prove2.me/submissions/bb58f161-3d38-4226-b662-30b72da3d3c7

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Theorems.Thm_UlmsTheorem_hillInvariant_add_overhangInvariant

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
    relativeUlmInvariant p S α + overhangInvariant (p := p) S α =
      markedGradedInvariant p S α :=
  hillInvariant_add_overhangInvariant p S α
end UlmsTheorem
