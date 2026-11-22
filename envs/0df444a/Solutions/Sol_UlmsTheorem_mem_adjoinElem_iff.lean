-- Prove2me | solution 1 for UlmsTheorem.mem_adjoinElem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:13.451669+00:00
-- url     : https://prove2.me/submissions/7431e624-9f53-4d3e-966a-a7df9ca1c638

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
public import Theorems.Thm_UlmsTheorem_adjoinElem_eq_sup_zmultiples

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
theorem _root_.solution {A : AddSubgroup G} {g x : G} :
    x ∈ adjoinElem A g ↔ ∃ a ∈ A, ∃ n : ℤ, a + n • g = x := by
  rw [adjoinElem_eq_sup_zmultiples]
  constructor
  · intro hx
    rcases (AddSubgroup.mem_sup).1 hx with ⟨a, ha, z, hz, hsum⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨n, rfl⟩
    exact ⟨a, ha, n, hsum⟩
  · rintro ⟨a, ha, n, rfl⟩
    exact AddSubgroup.add_mem_sup ha <| AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
end UlmsTheorem
