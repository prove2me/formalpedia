-- Prove2me | solution 1 for UlmsTheorem.markedGradedToHill_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:15.351605+00:00
-- url     : https://prove2.me/submissions/c6410ab2-6cbb-422e-b586-8c221c99b820

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
theorem _root_.solution (S : AddSubgroup G) (α : Ordinal) :
    Function.Surjective (markedGradedToHill (p := p) S α) := by
  exact Submodule.factor_surjective (markedGradedSubmodule_le_hillSubmodule p S α)
end UlmsTheorem
