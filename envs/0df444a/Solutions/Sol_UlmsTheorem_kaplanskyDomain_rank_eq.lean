-- Prove2me | solution 1 for UlmsTheorem.kaplanskyDomain_rank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:13.590285+00:00
-- url     : https://prove2.me/submissions/cac9c86c-0282-40df-bc77-f0bf64ba7c2a

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
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (kaplanskyDomainQuotient p s.A α) =
      Module.rank (ZMod p) (kaplanskyDomainQuotient p s.B α) := by
  let E := kaplanskyDomainEquiv p s
  let L :
      kaplanskyDomainQuotient p s.A α →ₗ[ZMod p]
        kaplanskyDomainQuotient p s.B α :=
    E.toAddMonoidHom.toZModLinearMap p
  let LE :
      kaplanskyDomainQuotient p s.A α ≃ₗ[ZMod p]
        kaplanskyDomainQuotient p s.B α :=
    LinearEquiv.ofBijective L E.bijective
  exact LinearEquiv.rank_eq LE
end UlmsTheorem
