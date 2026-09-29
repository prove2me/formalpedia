-- Prove2me | solution 1 for Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/aba56826-45ed-5fba-be51-9a6d38439efb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card

set_option autoImplicit false
universe u
open Module
open scoped IntermediateField Pointwise

private theorem mem_invariants_linHom_iff_T3a {k : Type*} [Field k] {Δ : Type*} [Group Δ]
    {VN : Type*} [AddCommGroup VN] [Module k VN] (N : Representation k Δ VN)
    {VW : Type*} [AddCommGroup VW] [Module k VW] (W : Representation k Δ VW)
    (φ : VN →ₗ[k] VW) : φ ∈ (N.linHom W).invariants ↔ ∀ (d : Δ) (v : VN), φ (N d v) = W d (φ v) := by
  rw [Representation.mem_invariants]
  constructor
  · intro h d v
    have := LinearMap.congr_fun (h d) (N d v)
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply] at this
    rw [← this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro h d
    apply LinearMap.ext
    intro v
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem solution
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {VN VA VB VC : Type*} [AddCommGroup VN] [Module k VN] [AddCommGroup VA] [Module k VA]
    [AddCommGroup VB] [Module k VB] [AddCommGroup VC] [Module k VC]
    [FiniteDimensional k VN] [FiniteDimensional k VB]
    (N : Representation k Δ VN) (A : Representation k Δ VA) (B : Representation k Δ VB) (C : Representation k Δ VC)
    (f : VA →ₗ[k] VB) (g : VB →ₗ[k] VC) (hf : ∀ d, f ∘ₗ A d = B d ∘ₗ f) (hg : ∀ d, g ∘ₗ B d = C d ∘ₗ g)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    finrank k (N.linHom B).invariants = finrank k (N.linHom A).invariants + finrank k (N.linHom C).invariants := by
  classical
  haveI : Invertible ((Fintype.card Δ : k)) := hΔ.invertible
  have hfd : ∀ (d : Δ) (a : VA), f (A d a) = B d (f a) := fun d a => LinearMap.congr_fun (hf d) a
  have hgd : ∀ (d : Δ) (b : VB), g (B d b) = C d (g b) := fun d b => LinearMap.congr_fun (hg d) b

  have hgmem : ∀ φ : (N.linHom B).invariants, g ∘ₗ (φ : VN →ₗ[k] VB) ∈ (N.linHom C).invariants := by
    intro φ
    rw [mem_invariants_linHom_iff_T3a]
    intro d v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_invariants_linHom_iff_T3a N B _).mp φ.2 d v, hgd]
  let G' : (N.linHom B).invariants →ₗ[k] (N.linHom C).invariants :=
    { toFun := fun φ => ⟨g ∘ₗ (φ : VN →ₗ[k] VB), hgmem φ⟩
      map_add' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_add])
      map_smul' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_smul]) }

  have hG'surj : Function.Surjective G' := by
    rintro ⟨φ, hφ⟩
    obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
    let ψ₀ : VN →ₗ[k] VB := s ∘ₗ φ
    let ψ : VN →ₗ[k] VB := (N.linHom B).averageMap ψ₀
    refine ⟨⟨ψ, (N.linHom B).averageMap_invariant ψ₀⟩, Subtype.ext ?_⟩
    show g ∘ₗ ψ = φ

    have hexp : ψ = ⅟(Fintype.card Δ : k) • ∑ d : Δ, (N.linHom B) d ψ₀ := by
      simp [ψ, Representation.averageMap, GroupAlgebra.average, map_sum, LinearMap.sum_apply]
    have hterm : ∀ d : Δ, g ∘ₗ ((N.linHom B) d ψ₀) = φ := by
      intro d
      apply LinearMap.ext
      intro v
      simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply]
      rw [hgd]
      erw [show g (s (φ (N d⁻¹ v))) = φ (N d⁻¹ v) from LinearMap.congr_fun hs _]
      rw [(mem_invariants_linHom_iff_T3a N C φ).mp hφ d⁻¹ v, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rw [hexp, LinearMap.comp_smul]
    have hsum : g ∘ₗ (∑ d : Δ, (N.linHom B) d ψ₀) = ∑ d : Δ, g ∘ₗ ((N.linHom B) d ψ₀) := by
      apply LinearMap.ext; intro v; simp [LinearMap.sum_apply, map_sum]
    rw [hsum]
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

  have hfmem : ∀ φ : (N.linHom A).invariants, f ∘ₗ (φ : VN →ₗ[k] VA) ∈ (N.linHom B).invariants := by
    intro φ
    rw [mem_invariants_linHom_iff_T3a]
    intro d v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_invariants_linHom_iff_T3a N A _).mp φ.2 d v, hfd]
  let F' : (N.linHom A).invariants →ₗ[k] (N.linHom B).invariants :=
    { toFun := fun φ => ⟨f ∘ₗ (φ : VN →ₗ[k] VA), hfmem φ⟩
      map_add' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_add])
      map_smul' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_smul]) }
  have hF'inj : Function.Injective F' := by
    intro φ φ' h
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply hinj
    exact LinearMap.congr_fun (congrArg Subtype.val h) v
  have hrange : LinearMap.range F' = LinearMap.ker G' := by
    ext φ
    constructor
    · rintro ⟨χ', rfl⟩
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      show g (f ((χ' : VN →ₗ[k] VA) v)) = 0
      exact hexact.apply_apply_eq_zero _
    · intro hφ
      have hφ0 : ∀ v, g ((φ : VN →ₗ[k] VB) v) = 0 := fun v =>
        LinearMap.congr_fun (congrArg Subtype.val (LinearMap.mem_ker.mp hφ)) v

      obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
      have hfr : ∀ v, f (r ((φ : VN →ₗ[k] VB) v)) = (φ : VN →ₗ[k] VB) v := by
        intro v
        obtain ⟨a, ha⟩ := (hexact _).mp (hφ0 v)
        rw [← ha, show r (f a) = a from LinearMap.congr_fun hr a]
      refine ⟨⟨r ∘ₗ (φ : VN →ₗ[k] VB), (mem_invariants_linHom_iff_T3a N A _).mpr fun d v => hinj ?_⟩, Subtype.ext (LinearMap.ext fun v => hfr v)⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hfd, hfr, hfr]
      exact (mem_invariants_linHom_iff_T3a N B _).mp φ.2 d v

  have hrn := LinearMap.finrank_range_add_finrank_ker G'
  rw [LinearMap.range_eq_top.mpr hG'surj, finrank_top, ← hrange, LinearMap.finrank_range_of_inj hF'inj] at hrn
  omega

end S_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
end P2MW
export P2MW.S_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card (solution)
