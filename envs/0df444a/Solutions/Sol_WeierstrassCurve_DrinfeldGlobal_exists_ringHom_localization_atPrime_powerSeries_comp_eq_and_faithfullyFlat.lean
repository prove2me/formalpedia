-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b22ee165-cd65-5681-9c57-c060b5bc1ec7

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_Module_FaithfullyFlat_of_isAdicComplete_of_forall_pow_maximalIdeal
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_sub_map_mem_maximalIdeal_pow_of_originChart_powerSeries
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace A4bAux

theorem mk'_mem_maximalIdeal_pow {R : Type*} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (n : ℕ) (a : R)
    (s : 𝔭.primeCompl) (ha : a ∈ 𝔭 ^ n) :
    IsLocalization.mk' (Localization.AtPrime 𝔭) a s ∈ maximalIdeal (Localization.AtPrime 𝔭) ^ n := by
  have hle : 𝔭 ≤ (maximalIdeal (Localization.AtPrime 𝔭)).comap (algebraMap R (Localization.AtPrime 𝔭)) :=
    le_of_eq (Localization.AtPrime.under_maximalIdeal (I := 𝔭)).symm
  have h3 : algebraMap R (Localization.AtPrime 𝔭) a ∈ maximalIdeal (Localization.AtPrime 𝔭) ^ n :=
    Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n ha)
  rw [IsLocalization.mk'_eq_mul_mk'_one (S := Localization.AtPrime 𝔭)]
  exact Ideal.mul_mem_right _ _ h3

theorem apply_eq_mul_lift_mk' {R P : Type*} [CommRing R] [CommRing P] (𝔭 : Ideal R) [𝔭.IsPrime] (g : R →+* P)
    (hg : ∀ y : 𝔭.primeCompl, IsUnit (g y)) (a : R) (s : 𝔭.primeCompl) :
    g a = g s * IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) hg
      (IsLocalization.mk' (Localization.AtPrime 𝔭) a s) :=
  (IsLocalization.lift_mk'_spec hg a _ s).mp rfl

end A4bAux

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    ∃ ψ : Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))) →+* PowerSeries T,
      ψ.comp (algebraMap (OriginChartRing W) _) = Φ ∧
      (letI : Algebra (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) (PowerSeries T) :=
          ψ.toAlgebra;
        Module.FaithfullyFlat (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) (PowerSeries T)) := by

  obtain ⟨f, hfbij, -, -⟩ := WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing (W : WeierstrassCurve.Projective T)
  haveI hA : IsNoetherianRing (OriginChartRing W) :=
    isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective f hfbij).symm

  have hunit : ∀ y : (Ideal.comap Φ (maximalIdeal (PowerSeries T))).primeCompl, IsUnit (Φ y) := by
    intro y
    by_contra h
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine ⟨IsLocalization.lift (M := (Ideal.comap Φ (maximalIdeal (PowerSeries T))).primeCompl) hunit,
    IsLocalization.lift_comp hunit, ?_⟩
  set ψ : Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))) →+* PowerSeries T :=
    IsLocalization.lift (M := (Ideal.comap Φ (maximalIdeal (PowerSeries T))).primeCompl) hunit with hψdef
  have hψalg : ∀ a : OriginChartRing W, ψ (algebraMap (OriginChartRing W) _ a) = Φ a := fun a =>
    IsLocalization.lift_eq hunit a
  letI : Algebra (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) (PowerSeries T) := ψ.toAlgebra
  haveI : IsNoetherianRing (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) :=
    IsLocalization.isNoetherianRing (Ideal.comap Φ (maximalIdeal (PowerSeries T))).primeCompl _ hA
  haveI : IsAdicComplete (maximalIdeal (PowerSeries T)) (PowerSeries T) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := T)

  have hmaple : (maximalIdeal (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))))) ≤
      Ideal.comap ψ (maximalIdeal (PowerSeries T)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap,
      IsLocalization.lift_comp]
  haveI : IsLocalHom (algebraMap (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) (PowerSeries T)) :=
    ((IsLocalRing.local_hom_TFAE ψ).out 3 0).mp hmaple

  have hsurj : ∀ (n : ℕ) (b : PowerSeries T), ∃ r : Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))),
      b - algebraMap _ (PowerSeries T) r ∈ maximalIdeal (PowerSeries T) ^ n := by
    intro n b
    obtain ⟨a, ha⟩ := WeierstrassCurve.DrinfeldGlobal.exists_sub_map_mem_maximalIdeal_pow_of_originChart_powerSeries
      W Φ hΦsc hΦx hΦz n b
    exact ⟨algebraMap (OriginChartRing W) _ a, by rw [RingHom.algebraMap_toAlgebra, hψalg]; exact ha⟩
  have hinj : ∀ (n : ℕ) (r : Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))),
      algebraMap _ (PowerSeries T) r ∈ maximalIdeal (PowerSeries T) ^ n →
        r ∈ maximalIdeal (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T)))) ^ n := by
    intro n r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.comap Φ (maximalIdeal (PowerSeries T))).primeCompl r
    refine A4bAux.mk'_mem_maximalIdeal_pow _ n a s
      (WeierstrassCurve.DrinfeldGlobal.mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow W Φ hΦsc hΦx hΦz n a ?_)
    rw [A4bAux.apply_eq_mul_lift_mk' _ Φ hunit a s]
    exact Ideal.mul_mem_left _ _ hr
  exact Module.FaithfullyFlat.of_isAdicComplete_of_forall_pow_maximalIdeal _ _ hinj hsurj

end S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat (solution)
