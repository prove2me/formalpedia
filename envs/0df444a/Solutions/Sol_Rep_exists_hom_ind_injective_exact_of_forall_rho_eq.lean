-- Prove2me | solution 1 for Rep.exists_hom_ind_injective_exact_of_forall_rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f3fd8d44-eeda-55bb-8c59-1d5fc9c7176d

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

namespace IndSes

universe u v w
variable {k : Type u} [CommRing k] {G : Type v} [Group G]

private lemma unit_apply_coe (N : Subgroup G) (B : Rep.{max v w} k G) (b : B) (g : G) :
    (((Rep.resCoindAdjunction k N.subtype).unit.app B).hom b).1 g = B.ρ g b := rfl

private lemma unit_injective (N : Subgroup G) (B : Rep.{max v w} k G) :
    Function.Injective ((Rep.resCoindAdjunction k N.subtype).unit.app B).hom := by
  intro b b' h
  have h1 : B.ρ 1 b = B.ρ 1 b' := congrArg (fun f : Rep.coind N.subtype (Rep.res N.subtype B) => f.1 1) h
  rwa [map_one, Module.End.one_apply, Module.End.one_apply] at h1

private lemma coind_ρ_eq_self (N : Subgroup G) [hNn : N.Normal] (B : Rep.{max v w} k G) (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (n : G) (hn : n ∈ N) (f : Rep.coind N.subtype (Rep.res N.subtype B)) :
    (Rep.coind N.subtype (Rep.res N.subtype B)).ρ n f = f := by
  apply Subtype.ext
  funext g
  change f.1 (g * n) = f.1 g
  have hmem : g * n * g⁻¹ ∈ N := hNn.conj_mem n hn g
  have h := f.2 ⟨g * n * g⁻¹, hmem⟩ g

  change f.1 (g * n * g⁻¹ * g) = B.ρ (g * n * g⁻¹) (f.1 g) at h
  rw [inv_mul_cancel_right] at h
  rw [h, hN _ hmem]

private lemma iso_hom_injective {X Y : Rep.{max v w} k G} (e : X ≅ Y) : Function.Injective e.hom.hom := by
  intro x y h
  have := congrArg e.inv.hom h
  change (e.hom ≫ e.inv).hom x = (e.hom ≫ e.inv).hom y at this
  rwa [e.hom_inv_id] at this

private lemma iso_inv_injective {X Y : Rep.{max v w} k G} (e : X ≅ Y) : Function.Injective e.inv.hom := iso_hom_injective e.symm

private def homAdd {X Y : Rep.{max v w} k G} (a : X ⟶ Y) : X →+ Y := a.hom.toLinearMap.toAddMonoidHom
private lemma homAdd_apply {X Y : Rep.{max v w} k G} (a : X ⟶ Y) (x : X) : homAdd a x = a.hom x := rfl

private lemma nsmul_coind_eq_zero (N : Subgroup G) (B : Rep.{max v w} k G) (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (f : Rep.coind N.subtype (Rep.res N.subtype B)) : p • f = 0 := by
  apply Subtype.ext
  funext g
  change p • f.1 g = 0
  exact hB _

section coker
variable {X Y : Rep.{max v w} k G} (f : X ⟶ Y)

private noncomputable abbrev cokerObj : Rep.{max v w} k G :=
  Rep.of (Representation.quotient Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨X.ρ g a, Rep.hom_comm_apply f g a⟩)

private noncomputable def cokerπ : Y ⟶ cokerObj f := Rep.ofHom ⟨Submodule.mkQ _, fun _ => rfl⟩

private lemma cokerπ_hom_apply (y : Y) : (cokerπ f).hom y = Submodule.Quotient.mk y := rfl

private lemma cokerπ_hom_surjective : Function.Surjective (cokerπ f).hom := Submodule.mkQ_surjective _

private lemma cokerπ_hom_apply_eq_zero_iff (y : Y) : (cokerπ f).hom y = 0 ↔ y ∈ LinearMap.range f.hom.toLinearMap := by
  rw [cokerπ_hom_apply, Submodule.Quotient.mk_eq_zero]

end coker

end IndSes

open IndSes in
theorem solution
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal] (B : Rep ℤ G) [Fintype B] (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b) :
    ∃ (ι : B ⟶ (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)) (B₁ : Rep ℤ G) (_ : Fintype B₁)
      (ρ : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B) ⟶ B₁),
      Function.Injective ι.hom ∧ Function.Exact ι.hom ρ.hom ∧ Function.Surjective ρ.hom ∧
      (∀ b : B₁, p • b = 0) ∧ (∀ g ∈ N, ∀ b : B₁, B₁.ρ g b = b) ∧
      (∀ g ∈ N, ∀ x : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B), ((Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)).ρ g x = x) := by
  classical
  haveI : N.FiniteIndex := inferInstance

  let A : Rep ℤ ↥N := Rep.res N.subtype B
  let e : Rep.ind N.subtype A ≅ Rep.coind N.subtype A := Rep.indCoindIso A
  let η : B ⟶ Rep.coind N.subtype A := (Rep.resCoindAdjunction ℤ N.subtype).unit.app B
  let ι : B ⟶ (Rep.indFunctor ℤ N.subtype).obj A := η ≫ e.inv
  have hιinj : Function.Injective ι.hom := fun b b' h => unit_injective N B (iso_inv_injective e h)

  have hNind : ∀ g ∈ N, ∀ x : (Rep.indFunctor ℤ N.subtype).obj A, ((Rep.indFunctor ℤ N.subtype).obj A).ρ g x = x := by
    intro g hg x
    apply iso_hom_injective e
    exact (Rep.hom_comm_apply e.hom g x).trans (coind_ρ_eq_self N B hN g hg (e.hom.hom x))

  let B₁ : Rep ℤ G := cokerObj ι
  let ρ₁ : (Rep.indFunctor ℤ N.subtype).obj A ⟶ B₁ := cokerπ ι
  have hsurj : Function.Surjective ρ₁.hom := cokerπ_hom_surjective ι
  have hexact : Function.Exact ι.hom ρ₁.hom := by
    intro y
    rw [cokerπ_hom_apply_eq_zero_iff]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, hx⟩

  haveI : Finite (Rep.coind N.subtype A) := Finite.of_injective (fun f : Rep.coind N.subtype A => f.1) Subtype.val_injective
  haveI : Finite ((Rep.indFunctor ℤ N.subtype).obj A) := Finite.of_injective _ (iso_hom_injective e)
  haveI : Finite B₁ := Finite.of_surjective _ hsurj
  refine ⟨ι, B₁, Fintype.ofFinite B₁, ρ₁, hιinj, hexact, hsurj, ?_, ?_, hNind⟩
  ·
    intro b
    obtain ⟨x, rfl⟩ := hsurj b
    change p • homAdd ρ₁ x = 0
    rw [← map_nsmul]
    have hx : p • x = 0 := by
      apply iso_hom_injective e
      have h1 : e.hom.hom (p • x) = p • e.hom.hom x := map_nsmul (homAdd e.hom) p x
      rw [h1, nsmul_coind_eq_zero N B p hB]
      exact (map_zero (homAdd e.hom)).symm
    rw [hx, map_zero]
  ·
    intro g hg b
    obtain ⟨x, rfl⟩ := hsurj b
    rw [← Rep.hom_comm_apply, hNind g hg]

end S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq
end P2MW
export P2MW.S_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq (solution)
