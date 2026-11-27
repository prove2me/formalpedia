-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:00.648607+00:00
-- url     : https://prove2.me/submissions/d8a08123-6c32-4453-bd57-d2188e537a6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientLemmas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCoefficientLemmas_torsion_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open IsotropicCoefficientLemmas
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : IsotropicCoefficientSplitting (E := E) := by
  intro r X ξ hξ
  classical
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have hle : Mp X ξ ≤ X.Λ := fun μ h => h.1
  haveI : Module.Finite (𝓞 E) (Mp X ξ) := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h1 : ((Mp X ξ).comap X.Λ.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map X.Λ.subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Module.Finite.iff_fg.2 h2
  haveI : Module.Flat (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_bot X ξ)
  haveI : Module.FinitePresentation (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (Mp X ξ ⧸ Nx X ξ) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Nx X ξ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  set ρ : Mp X ξ →ₗ[𝓞 E] Mp X ξ := LinearMap.id - s ∘ₗ (Nx X ξ).mkQ with hρdef
  have hρN : ∀ m, ∃ e : E, ((ρ m : Mp X ξ) : Fin r → E) = e • ξ := by
    intro m
    have h1 : (Nx X ξ).mkQ (s ((Nx X ξ).mkQ m)) = (Nx X ξ).mkQ m := LinearMap.congr_fun hs _
    have h2 : (Nx X ξ).mkQ (ρ m) = 0 := by
      rw [hρdef, LinearMap.sub_apply, map_sub, LinearMap.id_apply, LinearMap.comp_apply, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 h2
  choose coef hcoef using hρN
  have hρid : ∀ m ∈ Nx X ξ, ρ m = m := by
    intro m hm
    have : (Nx X ξ).mkQ m = 0 := (Submodule.Quotient.mk_eq_zero _).2 hm
    simp [hρdef, this]
  have huniq : ∀ e e' : E, e • ξ = e' • ξ → e = e' := fun e e' h => smul_left_injective E hξ0 h
  have hmemMp : ∀ μ ∈ X.Λp ξ, μ ∈ Mp X ξ := fun μ h => ⟨h.1, h.2⟩
  refine ⟨fun μ => if h : μ ∈ Mp X ξ then coef ⟨μ, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    simp only [dif_pos (hmemMp μ hμ)]
    rw [← hcoef]
    exact (ρ _).2.1
  · intro μ hμ μ' hμ'
    have hs' := (Mp X ξ).add_mem (hmemMp μ hμ) (hmemMp μ' hμ')
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ), dif_pos (hmemMp μ' hμ')]
    apply huniq
    rw [← hcoef, add_smul, ← hcoef, ← hcoef]
    have : (⟨μ + μ', hs'⟩ : Mp X ξ) = ⟨μ, hmemMp μ hμ⟩ + ⟨μ', hmemMp μ' hμ'⟩ := rfl
    rw [this, map_add]
    rfl
  · intro α μ hμ
    have hs' : (α : E) • μ ∈ Mp X ξ := by
      rw [← smul_O]
      exact (Mp X ξ).smul_mem α (hmemMp μ hμ)
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ)]
    apply huniq
    rw [← hcoef, mul_smul, ← hcoef]
    have : (⟨(α : E) • μ, hs'⟩ : Mp X ξ) = α • ⟨μ, hmemMp μ hμ⟩ := Subtype.ext (smul_O α μ).symm
    rw [this, map_smul, Submodule.coe_smul, smul_O]
  · intro e he
    have hmem : e • ξ ∈ Mp X ξ := ⟨he, by rw [herm_smul_left, hξ.2.1, mul_zero]⟩
    simp only [dif_pos hmem]
    apply huniq
    rw [← hcoef, hρid _ ⟨e, rfl⟩]
end ReciprocityTheory.ChartRestriction.G.FD
