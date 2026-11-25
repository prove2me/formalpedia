-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_multAt_eq_localQuotLength_of_083cc3b8006e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:23.687036+00:00
-- url     : https://prove2.me/submissions/cbdf85cb-dbc3-4f5e-8bf0-3af47c7f5319

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_prod_X_pow_44da1a552808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_C_locB_c0010f784358
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_eq_zero_iff_8082885ee0d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_betaB_mem_maximalIdeal_iff_8d6ed7f06979
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_exists_betaB_mul_eq_45dd53d7220e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_localizedModule_quot_eq_8af71d39845c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_quot_map_eq_3ef1ee9624d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


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
variable {O : Type*} [CommRing O] [IsDomain O]
  {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
include hγ
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution [hVp : V.IsPrime] (hε : Function.Surjective ε)
    (W : Ideal (MvPolynomial (Coord n) ℤ)) (hW : ∀ F, γ F = 0 ↔ F ∈ W)
    (hV : ∀ v ∈ V, ∀ e, weightedHomogeneousComponent (coordDeg n) e v ∈ V)
    (hD : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
      ε F ∈ V.map ε → F ∈ V)
    (c : (k : ι) → Fin (n k + 1)) (hXc : ∀ k, ε (X ⟨k, c k⟩) = 1)
    (hXV : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) {s : MvPolynomial (Coord n) ℤ}
    {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a) :
    Geo.multAt (W ⊔ Ideal.span {s}) V = localQuotLength (V.map ε) (ε s) := by
  classical
  have hmax := betaB_mem_maximalIdeal_iff ε γ hγ V hV hD
  have hgood := exists_betaB_mul_eq ε γ hγ V hε c hXc hXV hmax
  have hker : ∀ F, betaB γ (V.map ε) F = 0 ↔ F ∈ W := fun F ↦
    (betaB_eq_zero_iff ε γ V F).trans (hW F)
  have hunit : ∀ t : V.primeCompl, IsUnit (betaB γ (V.map ε) t) := fun t ↦ by
    by_contra h
    exact t.2 ((hmax t).mp ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)))
  let algAB : Algebra (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) :=
    (IsLocalization.lift (M := (V.map ε).primeCompl) (S := Localization.AtPrime (V.map ε))
      (isUnit_C_locB (ι := ι) (V.map ε))).toAlgebra
  have : IsScalarTower O (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq O (MvPolynomial ι O) (locB ι (V.map ε)), algebraMap_eq]
      exact (IsLocalization.lift_comp (isUnit_C_locB (ι := ι) (V.map ε))).symm)
  have : Module.Flat (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (V.map ε)) (V.map ε).primeCompl
      (locB ι (V.map ε))).mpr inferInstance
  have hmaxA : (maximalIdeal (Localization.AtPrime (V.map ε))).map
      (algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε))) =
      maximalIdeal (locB ι (V.map ε)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq O (MvPolynomial ι O),
      ← Ideal.map_map, algebraMap_eq]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have : IsLocalHom (algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε))) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have h2 : algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε)) a ∈
        maximalIdeal (locB ι (V.map ε)) := by
      rw [← hmaxA]
      exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna))
    exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h2) ha
  have hI : Ideal.span {betaB γ (V.map ε) s} =
      (Ideal.span {algebraMap O (Localization.AtPrime (V.map ε)) (ε s)}).map
        (algebraMap (Localization.AtPrime (V.map ε)) (locB ι (V.map ε))) := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply O (MvPolynomial ι O) (locB ι (V.map ε)), algebraMap_eq,
      betaB, RingHom.comp_apply, hγ hs, map_mul,
      Ideal.span_singleton_mul_right_unit (isUnit_prod_X_pow _ a)]
  rw [Geo.multAt, dif_pos hVp,
    length_localizedModule_quot_eq (betaB γ (V.map ε)) V W s hker hunit hgood, hI,
    length_quot_map_eq hmaxA]
  rfl
end GroundTheory.Heights₂.Heights.OrbitChartMult
