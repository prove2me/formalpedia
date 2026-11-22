-- Prove2me | solution 1 for ReciprocityTheory.Gal.exists_valuationSubring_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:03.063053+00:00
-- url     : https://prove2.me/submissions/710d4482-8ec6-416b-9e9f-015dd05a04e1

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA

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
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring Ω, ∀ x : 𝓞 F,
      A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  classical
  let φ : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hφ : Function.Injective φ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hu : ∀ y : v.asIdeal.primeCompl, IsUnit (φ y) := by
    intro y
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply y.2
    have h1 : (y : 𝓞 F) = 0 := hφ (h0.trans (map_zero φ).symm)
    rw [h1]
    exact v.asIdeal.zero_mem
  let f : (Localization.AtPrime v.asIdeal) →+* Ω := IsLocalization.lift (M := v.asIdeal.primeCompl) hu
  have hf : ∀ z : 𝓞 F, f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) z) = φ z := fun z => IsLocalization.lift_eq hu z
  have hfi : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro hab
      rw [IsLocalization.injective (M := v.asIdeal.primeCompl) (S := (Localization.AtPrime v.asIdeal))
        (Ideal.primeCompl_le_nonZeroDivisors _) hab]
    · intro hab
      rw [hφ hab]
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  rw [LocalSubring.le_def] at hB
  obtain ⟨hle, hloc⟩ := hB
  haveI := hloc
  refine ⟨B, fun x => ?_⟩
  have hmem : φ x ∈ B := hle ⟨algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x, hf x⟩
  let bx : B := ⟨φ x, hmem⟩
  have hv : B.valuation (algebraMap F Ω (x : F)) = B.valuation (bx : Ω) := rfl
  rw [hv, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hx
    apply hnu
    have h1 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) :=
      IsLocalization.map_units (Localization.AtPrime v.asIdeal) (⟨x, hx⟩ : v.asIdeal.primeCompl)
    have h3 := (h1.map f.rangeRestrict).map (Subring.inclusion hle)
    rw [show f.rangeRestrict (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) =
      (⟨φ x, ⟨_, hf x⟩⟩ : f.range) from Subtype.ext (hf x)] at h3
    exact h3
  · intro hx hu'
    have h1 := isUnit_of_map_unit (Subring.inclusion hle) ⟨φ x, ⟨_, hf x⟩⟩ hu'
    obtain ⟨w, hw⟩ := h1.exists_right_inv
    obtain ⟨r, hr⟩ := w.2
    have h4 : f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x * r) = f 1 := by
      rw [map_mul, hf, hr, map_one]
      exact congrArg Subtype.val hw
    have h5 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) := ⟨⟨_, r, hfi h4, (mul_comm _ _).trans (hfi h4)⟩, rfl⟩
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal x).1 h5 hx
end ReciprocityTheory.Gal
