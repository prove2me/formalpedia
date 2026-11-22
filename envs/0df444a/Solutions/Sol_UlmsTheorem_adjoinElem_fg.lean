-- Prove2me | solution 1 for UlmsTheorem.adjoinElem_fg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:21.786424+00:00
-- url     : https://prove2.me/submissions/2f5688ef-cc2f-41d1-9b45-f43c79c59d83

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
theorem _root_.solution {A : AddSubgroup G} (hAfg : A.FG) (g : G) :
    (adjoinElem A g).FG := by
  classical
  unfold adjoinElem
  refine hAfg.sup ?_
  exact (AddSubgroup.fg_iff _).2 ⟨{g}, rfl, Set.finite_singleton g⟩
end UlmsTheorem
