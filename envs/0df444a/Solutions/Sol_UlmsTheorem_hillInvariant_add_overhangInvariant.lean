-- Prove2me | solution 1 for UlmsTheorem.hillInvariant_add_overhangInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:49.903203+00:00
-- url     : https://prove2.me/submissions/b5b4dc32-5343-4917-8873-b1a1823f670b

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
    hillInvariant p S α + overhangInvariant (p := p) S α =
      markedGradedInvariant p S α := by
  unfold hillInvariant overhangInvariant markedGradedInvariant
  unfold hillQuotient markedGradedQuotient overhangSubmodule
  rw [← (Submodule.quotientQuotientEquivQuotient
    (markedGradedSubmodule p S α) (hillSubmodule p S α)
    (markedGradedSubmodule_le_hillSubmodule p S α)).rank_eq]
  exact Submodule.rank_quotient_add_rank (overhangSubmodule p S α)
end UlmsTheorem
