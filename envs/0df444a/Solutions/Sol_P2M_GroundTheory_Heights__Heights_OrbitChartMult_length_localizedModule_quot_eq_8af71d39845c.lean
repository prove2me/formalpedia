-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_localizedModule_quot_eq_8af71d39845c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:17.305336+00:00
-- url     : https://prove2.me/submissions/3906e507-77d5-4e3a-8a7f-a26a969204f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {R B : Type*} [CommRing R] [CommRing B]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (β : R →+* B) (V W : Ideal R) [hVp : V.IsPrime] (s : R)
    (hker : ∀ F, β F = 0 ↔ F ∈ W) (hunit : ∀ t : V.primeCompl, IsUnit (β t))
    (hgood : ∀ b, ∃ F t, t ∉ V ∧ β t * b = β F) :
    Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (R ⧸ (W ⊔ Ideal.span {s}))) =
      Module.length B (B ⧸ Ideal.span {β s}) := by
  classical
  let algV : Algebra (Localization.AtPrime V) B :=
    (IsLocalization.lift (M := V.primeCompl) (S := Localization.AtPrime V) hunit).toAlgebra
  let algR : Algebra R B := β.toAlgebra
  have : IsScalarTower R (Localization.AtPrime V) B :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hunit).symm
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime V) B) := by
    intro b
    obtain ⟨F, t, ht, e⟩ := hgood b
    refine ⟨IsLocalization.mk' _ F (⟨t, ht⟩ : V.primeCompl), ?_⟩
    show IsLocalization.lift hunit (IsLocalization.mk' _ F (⟨t, ht⟩ : V.primeCompl)) = b
    rw [IsLocalization.lift_mk'_spec]
    exact e.symm
  let I : Ideal B := Ideal.span {β s}
  let J : Ideal R := W ⊔ Ideal.span {s}
  let f : R →ₗ[R] B ⧸ I := ((Ideal.Quotient.mkₐ R I).comp (Algebra.ofId R B)).toLinearMap
  have hf : ∀ F, f F = Ideal.Quotient.mk I (β F) := fun F ↦ rfl
  have hJ : J ≤ LinearMap.ker f := by
    refine sup_le (fun F hF ↦ ?_) (Ideal.span_le.mpr fun F hF ↦ ?_)
    · rw [LinearMap.mem_ker, hf, (hker F).mpr hF, map_zero]
    · rw [Set.mem_singleton_iff] at hF
      subst hF
      rw [SetLike.mem_coe, LinearMap.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
  let g : (R ⧸ J) →ₗ[R] B ⧸ I := Submodule.liftQ J f hJ
  have hg : ∀ F, g (Ideal.Quotient.mk J F) = Ideal.Quotient.mk I (β F) := fun F ↦ rfl
  have hsmul : ∀ (r : R) (y : B ⧸ I), r • y = β r • y := fun r y ↦ (algebraMap_smul _ r y).symm
  have hloc : IsLocalizedModule V.primeCompl g := by
    constructor
    · intro t
      rw [Module.End.isUnit_iff]
      obtain ⟨u, hu⟩ := hunit t
      have hsm : ∀ y : B ⧸ I, (algebraMap R (Module.End R (B ⧸ I)) t) y = (u : B) • y := fun y ↦ by
        rw [Module.algebraMap_end_apply, hsmul, hu]
      constructor
      · intro y z h
        rw [hsm, hsm] at h
        have := congrArg (fun w ↦ (↑u⁻¹ : B) • w) h
        simpa [smul_smul] using this
      · intro y
        refine ⟨(↑u⁻¹ : B) • y, ?_⟩
        rw [hsm, smul_smul, Units.mul_inv, one_smul]
    · intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨F, t, ht, e⟩ := hgood b
      refine ⟨(Ideal.Quotient.mk J F, ⟨t, ht⟩), ?_⟩
      show (t : R) • Ideal.Quotient.mk I b = g (Ideal.Quotient.mk J F)
      rw [hsmul, hg, ← e]
      rfl
    · intro y₁ y₂ h
      obtain ⟨F₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨F₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      rw [hg, hg, Ideal.Quotient.eq, ← map_sub] at h
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp h
      obtain ⟨G, t, ht, e⟩ := hgood b
      refine ⟨⟨t, ht⟩, ?_⟩
      have hmem : t * (F₁ - F₂) - G * s ∈ W := by
        rw [← hker, map_sub, map_mul, map_mul, ← hb, ← e]
        ring
      show Ideal.Quotient.mk J (t * F₁) = Ideal.Quotient.mk J (t * F₂)
      rw [Ideal.Quotient.eq]
      have e2 : t * F₁ - t * F₂ = (t * (F₁ - F₂) - G * s) + G * s := by ring
      rw [e2]
      exact J.add_mem (Ideal.mem_sup_left hmem)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  let eV := (IsLocalizedModule.iso V.primeCompl g).extendScalarsOfIsLocalization V.primeCompl
    (Localization.AtPrime V)
  rw [eV.length_eq, Module.length_eq_of_surjective hsurj]
end GroundTheory.Heights₂.Heights.OrbitChartMult
