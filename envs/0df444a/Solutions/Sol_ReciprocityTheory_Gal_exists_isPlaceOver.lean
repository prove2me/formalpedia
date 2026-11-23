-- Prove2me | solution 1 for ReciprocityTheory.Gal.exists_isPlaceOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:52.587195+00:00
-- url     : https://prove2.me/submissions/d21a283a-363d-47cc-9680-574d819a13e9

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (Ω)
namespace ReciprocityTheory.Gal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring (Ω), IsPlaceOver A v := by
  classical
  have hinj : Function.Injective (algebraMap F Ω) := (algebraMap F Ω).injective
  haveI hV : IsLocalRing (v.valuation F).valuationSubring.toSubring :=
    inferInstanceAs (IsLocalRing (v.valuation F).valuationSubring)
  haveI hS : IsLocalRing ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) :=
    IsLocalRing.of_surjective'
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).toRingHom
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).surjective
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring
    (LocalSubring.mk ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) : LocalSubring Ω)
  obtain ⟨hsub, hloc⟩ := hB
  have hfx : ∀ z : F, v.valuation F z ≤ 1 → algebraMap F Ω z ∈ B := fun z hz =>
    hsub (Subring.mem_map.mpr ⟨z, hz, rfl⟩)
  have hle : ∀ r : 𝓞 F, v.valuation F (r : F) ≤ 1 := fun r => v.valuation_le_one r
  have hlt : ∀ r : 𝓞 F, v.valuation F (r : F) < 1 ↔ r ∈ v.asIdeal := fun r =>
    v.valuation_lt_one_iff_mem r
  refine ⟨B, ?_⟩
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  intro x
  constructor
  · intro h
    by_contra hx
    have hx1 : v.valuation F (x : F) = 1 := le_antisymm (hle x) (not_lt.mp (mt (hlt x).mp hx))
    have hx0 : (x : F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx1
      exact zero_ne_one hx1
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hinv : v.valuation F ((x : F)⁻¹) ≤ 1 := by rw [map_inv₀, hx1, inv_one]
    have hmem : algebraMap F Ω ((x : F)⁻¹) ∈ B := hfx _ hinv
    rw [map_inv₀] at hmem
    have h1 : B.valuation (algebraMap F Ω (x : F))⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hmem
    have h2 := (Valuation.one_lt_val_iff B.valuation (inv_ne_zero hne)).mpr (by rwa [inv_inv])
    exact absurd h1 (not_le.mpr h2)
  · intro hx
    by_contra hnot
    have hxlt := (hlt x).mpr hx
    by_cases hx0 : (x : F) = 0
    · apply hnot
      rw [hx0, map_zero, map_zero]
      exact zero_lt_one
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hyB : algebraMap F Ω (x : F) ∈ B := hfx _ (hle x)
    have hyv : B.valuation (algebraMap F Ω (x : F)) = 1 :=
      le_antisymm ((B.valuation_le_one_iff _).mpr hyB) (not_lt.mp hnot)
    have hyinvB : (algebraMap F Ω (x : F))⁻¹ ∈ B := by
      rw [← B.valuation_le_one_iff, map_inv₀, hyv, inv_one]
    have hyS : algebraMap F Ω (x : F) ∈ (v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω) :=
      Subring.mem_map.mpr ⟨_, hle x, rfl⟩
    have hunit : IsUnit (Subring.inclusion hsub ⟨_, hyS⟩) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hyinvB⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
    have ht := ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
      ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).2
    have hmul : algebraMap F Ω (x : F) *
        ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
          ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).1 = 1 := by
      have h3 := congrArg Subtype.val u.mul_inv
      rw [hu] at h3
      exact h3
    obtain ⟨z, hz, hzt⟩ := Subring.mem_map.mp ht
    have hzx : z = (x : F)⁻¹ := by
      apply hinj
      rw [hzt, map_inv₀]
      exact eq_inv_of_mul_eq_one_right hmul
    have hzle : v.valuation F z ≤ 1 := hz
    rw [hzx] at hzle
    have h4 := (Valuation.one_lt_val_iff (v.valuation F) (inv_ne_zero hx0)).mpr (by rwa [inv_inv])
    exact absurd hzle (not_le.mpr h4)
end ReciprocityTheory.Gal
