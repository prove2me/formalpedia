-- Prove2me | solution 1 for UlmsTheorem.kaplanskyDomain_module_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:17.6706+00:00
-- url     : https://prove2.me/submissions/53843b4a-2048-4d9c-bd1c-5e4a071ba45e

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
    (S : AddSubgroup G) (hSfinite : Set.Finite (S : Set G))
    (α : Ordinal.{0}) :
    Module.Finite (ZMod p) (kaplanskyDomainQuotient p S α) := by
  have hstar :
      Set.Finite (kaplanskyStar p S α : Set G) :=
    hSfinite.subset (by
      intro x hx
      exact hx.1)
  let _ : Finite (kaplanskyStar p S α) := hstar.to_subtype
  let _ : Finite (kaplanskyDomainQuotient p S α) :=
    Finite.of_surjective
      (QuotientAddGroup.mk' (stageAtSuccInStar p S α))
      (QuotientAddGroup.mk'_surjective _)
  apply Module.Finite.of_fg_top
  rw [← Submodule.span_univ]
  exact Submodule.fg_span Set.finite_univ
end UlmsTheorem
