-- Prove2me | solution 1 for Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c1b64f28-8c4a-5d14-8dc0-83a3a2558135

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top

set_option autoImplicit false

open scoped BigOperators

namespace LatticeEigenInt

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem isAddTorsionFree_submodule (Λ : Submodule ℤ V) : IsAddTorsionFree Λ := by
  refine ⟨fun n hn a b hab => ?_⟩
  apply Subtype.ext
  have h : (n : ℂ) • ((a : V) - b) = 0 := by
    have hab' : n • (a : V) = n • (b : V) := by
      have := congrArg (fun x : Λ => (x : V)) hab
      simpa using this
    rw [smul_sub, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hab', sub_self]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have := (smul_eq_zero.mp h).resolve_left hn'
  exact sub_eq_zero.mp this

theorem moduleFinite_end (Λ : Submodule ℤ V) (hΛfg : Λ.FG) : Module.Finite ℤ (Λ →ₗ[ℤ] Λ) := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛfg
  haveI : IsAddTorsionFree Λ := isAddTorsionFree_submodule Λ
  haveI : Module.IsTorsionFree ℤ Λ := inferInstance
  haveI : Module.Free ℤ Λ := inferInstance
  exact Module.Finite.linearMap ℤ ℤ Λ Λ

def opAlg {J : Type*} (S : J → V →ₗ[ℂ] V) : Subalgebra ℤ (V →ₗ[ℂ] V) :=
  Algebra.adjoin ℤ (Set.range S)

theorem opAlg_preserves (Λ : Submodule ℤ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) :
    ∀ T ∈ opAlg S, ∀ x ∈ Λ, T x ∈ Λ := by
  intro T hT
  refine Algebra.adjoin_induction (p := fun T _ => ∀ x ∈ Λ, T x ∈ Λ) ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨j, rfl⟩ x hx; exact hS j x hx
  · intro n x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact Λ.smul_mem n hx
  · intro T₁ T₂ _ _ h₁ h₂ x hx
    rw [LinearMap.add_apply]; exact Λ.add_mem (h₁ x hx) (h₂ x hx)
  · intro T₁ T₂ _ _ h₁ h₂ x hx
    rw [Module.End.mul_apply]; exact h₁ _ (h₂ x hx)

noncomputable def res (Λ : Submodule ℤ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) : opAlg S →ₗ[ℤ] (Λ →ₗ[ℤ] Λ) where
  toFun T := (T.1.restrictScalars ℤ).restrict (fun x hx => opAlg_preserves Λ S hS T.1 T.2 x hx)
  map_add' T₁ T₂ := by ext x; rfl
  map_smul' n T := by ext x; simp [LinearMap.restrict_apply]

theorem res_apply (Λ : Submodule ℤ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) (T : opAlg S) (x : Λ) :
    ((res Λ S hS T x : Λ) : V) = T.1 x := rfl

theorem res_injective (Λ : Submodule ℤ V) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) :
    Function.Injective (res Λ S hS) := by
  intro T₁ T₂ h
  apply Subtype.ext
  apply LinearMap.ext_on hΛspan
  intro x hx
  have := congrArg (fun F : Λ →ₗ[ℤ] Λ => ((F ⟨x, hx⟩ : Λ) : V)) h
  simpa [res_apply] using this

theorem moduleFinite_opAlg [FiniteDimensional ℂ V] (Λ : Submodule ℤ V) (hΛfg : Λ.FG)
    (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) :
    Module.Finite ℤ (opAlg S) := by
  haveI := moduleFinite_end Λ hΛfg
  exact Module.Finite.of_injective (res Λ S hS) (res_injective Λ hΛspan S hS)

def eigAlg (v : V) : Subalgebra ℤ (V →ₗ[ℂ] V) where
  carrier := {T | ∃ μ : ℂ, T v = μ • v}
  mul_mem' := by
    rintro T₁ T₂ ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
    refine ⟨μ₂ * μ₁, ?_⟩
    rw [Module.End.mul_apply, h₂, map_smul, h₁, smul_smul]
  add_mem' := by
    rintro T₁ T₂ ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
    exact ⟨μ₁ + μ₂, by rw [LinearMap.add_apply, h₁, h₂, add_smul]⟩
  algebraMap_mem' n := ⟨n, by
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      Int.cast_smul_eq_zsmul]⟩

theorem mem_eigAlg {v : V} {T : V →ₗ[ℂ] V} : T ∈ eigAlg v ↔ ∃ μ : ℂ, T v = μ • v := Iff.rfl

noncomputable def ev (v : V) (T : eigAlg v) : ℂ := (mem_eigAlg.mp T.2).choose

theorem ev_spec (v : V) (T : eigAlg v) : T.1 v = ev v T • v := (mem_eigAlg.mp T.2).choose_spec

theorem ev_unique {v : V} (hv0 : v ≠ 0) (T : eigAlg v) {μ : ℂ} (h : T.1 v = μ • v) :
    ev v T = μ := by
  have h1 := ev_spec v T
  rw [h] at h1
  exact (smul_left_injective ℂ hv0 h1).symm

noncomputable def evHom {v : V} (hv0 : v ≠ 0) : eigAlg v →+* ℂ where
  toFun := ev v
  map_one' := ev_unique hv0 _ (by simp)
  map_mul' T₁ T₂ := ev_unique hv0 _ (by
    show T₁.1 (T₂.1 v) = _
    rw [ev_spec v T₂, map_smul, ev_spec v T₁, smul_smul, mul_comm])
  map_zero' := ev_unique hv0 _ (by simp)
  map_add' T₁ T₂ := ev_unique hv0 _ (by
    show T₁.1 v + T₂.1 v = _
    rw [ev_spec v T₁, ev_spec v T₂, add_smul])

theorem main [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) := by
  haveI := moduleFinite_opAlg Λ hΛfg hΛspan S hS

  have hle : opAlg S ≤ eigAlg v := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    exact ⟨lam j, hv j⟩

  let χ : opAlg S →+* ℂ := (evHom hv0).comp (Subalgebra.inclusion hle).toRingHom

  let χl : opAlg S →ₗ[ℤ] ℂ := χ.toIntAlgHom.toLinearMap

  have hfin : Module.Finite ℤ (LinearMap.range χl) := Module.Finite.range χl
  have hsub : (Subalgebra.toSubmodule (Algebra.adjoin ℤ (Set.range lam))) ≤ LinearMap.range χl := by

    have hr : LinearMap.range χl = Subalgebra.toSubmodule (χ.toIntAlgHom.range) := by
      ext z
      simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, AlgHom.mem_range]
      rfl
    rw [hr]
    apply Subalgebra.toSubmodule.monotone
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨S j, Algebra.subset_adjoin ⟨j, rfl⟩⟩, ?_⟩
    show ev v ⟨S j, _⟩ = lam j
    exact ev_unique hv0 _ (hv j)

  haveI : IsNoetherian ℤ (LinearMap.range χl) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  let f : Algebra.adjoin ℤ (Set.range lam) →ₗ[ℤ] LinearMap.range χl :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun n x => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun z : LinearMap.range χl => (z : ℂ)) hxy
    exact this
  exact Module.Finite.of_injective f hf

end LatticeEigenInt

theorem solution
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) :=
  LatticeEigenInt.main Λ hΛfg hΛspan S hS lam v hv0 hv

end S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
end P2MW
export P2MW.S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top (solution)
