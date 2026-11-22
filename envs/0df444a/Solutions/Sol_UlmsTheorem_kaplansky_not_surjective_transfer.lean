-- Prove2me | solution 1 for UlmsTheorem.kaplansky_not_surjective_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:55.883444+00:00
-- url     : https://prove2.me/submissions/4c41c91d-0598-4029-a199-d640582ab92d

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
public import Theorems.Thm_UlmsTheorem_kaplanskyMap_injective
public import Theorems.Thm_UlmsTheorem_kaplanskyDomain_rank_eq
public import Theorems.Thm_UlmsTheorem_kaplanskyDomain_module_finite

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
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    (hinv :
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hGroom : ¬ Function.Surjective (kaplanskyMap p s.A α)) :
    ¬ Function.Surjective (kaplanskyMap p s.B α) := by
  intro hHsurj
  let DA := kaplanskyDomainQuotient p s.A α
  let DB := kaplanskyDomainQuotient p s.B α
  let PG := ulmQuotient p α (G := G)
  let PH := ulmQuotient p α (G := H)
  let UG : DA →ₗ[ZMod p] PG :=
    kaplanskyLinearMap p s.A α (kaplanskyMap p s.A α)
  let UH : DB →ₗ[ZMod p] PH :=
    kaplanskyLinearMap p s.B α (kaplanskyMap p s.B α)
  let _ : Module.Finite (ZMod p) DA :=
    kaplanskyDomain_module_finite p s.A s.hAfinite α
  let _ : Module.Finite (ZMod p) DB :=
    kaplanskyDomain_module_finite p s.B s.hBfinite α
  have hUHinj : Function.Injective UH :=
    kaplanskyMap_injective p s.B α
  have hUHsurj : Function.Surjective UH := hHsurj
  let EH : DB ≃ₗ[ZMod p] PH :=
    LinearEquiv.ofBijective UH ⟨hUHinj, hUHsurj⟩
  let _ : Module.Finite (ZMod p) PH :=
    Module.Finite.of_surjective UH hUHsurj
  have hrankDA_PH :
      Module.rank (ZMod p) DA = Module.rank (ZMod p) PH := by
    calc
      Module.rank (ZMod p) DA = Module.rank (ZMod p) DB :=
        kaplanskyDomain_rank_eq p s
      _ = Module.rank (ZMod p) PH := LinearEquiv.rank_eq EH
  have hrankDA_PG :
      Module.rank (ZMod p) DA = Module.rank (ZMod p) PG := by
    exact hrankDA_PH.trans hinv.symm
  have hrankPG_nat :
      Module.rank (ZMod p) PG =
        (Module.finrank (ZMod p) DA : Cardinal) := by
    exact hrankDA_PG.symm.trans
      (Module.finrank_eq_rank (R := ZMod p) (M := DA)).symm
  let _ : Module.Finite (ZMod p) PG :=
    Module.finite_of_rank_eq_nat hrankPG_nat
  have hfinPG :
      Module.finrank (ZMod p) PG = Module.finrank (ZMod p) DA :=
    Module.finrank_eq_of_rank_eq hrankPG_nat
  have hUGinj : Function.Injective UG :=
    kaplanskyMap_injective p s.A α
  have hUGsurj : Function.Surjective UG :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinPG.symm).mp hUGinj
  exact hGroom hUGsurj
end UlmsTheorem
