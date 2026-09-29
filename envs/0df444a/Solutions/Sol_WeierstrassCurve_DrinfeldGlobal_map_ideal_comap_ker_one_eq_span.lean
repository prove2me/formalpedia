-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_ker_one_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/080c2c42-eed6-5b5d-b2e2-5b34969bf7b4

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_ideal_comap_specMap_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span.WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve p2m_export "WeierstrassCurve" "map map_id map_injective DrinfeldGlobal.IsOriginChartSection DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker DrinfeldGlobal.ker_eq_span_of_originChartRing" namespace DrinfeldGlobal p2m_export "WeierstrassCurve.DrinfeldGlobal" "base Section torsionIdeal OriginChartRing originChartι xOverY zOverY IsOriginChartSection IsOriginChartSection.map_ideal_comap_ker_eq_ker ker_eq_span_of_originChartRing" namespace SectionPreimageO end WeierstrassCurve.DrinfeldGlobal.SectionPreimageO
p2m_open_scoped "WeierstrassCurve WeierstrassCurve.DrinfeldGlobal" in

theorem WeierstrassCurve.DrinfeldGlobal.SectionPreimageO.apply_sc_eq {T : Type u} [CommRing T]
    (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection P χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := P.2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T ↦ g.hom t) h3
  simpa using h4

open WeierstrassCurve.DrinfeldGlobal.SectionPreimageO in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR W))
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    {B : Type u} [CommRing B] (χ : OriginChartRing W →+* B) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      (((Scheme.Hom.ker (G.one (𝟙 _)).1).comap (Spec.map (CommRingCat.ofHom χ) ≫ originChartι W)).ideal
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      Ideal.span {χ (xOverY W), χ (zOverY W)} := by
  obtain ⟨χ₀, hχ₀, h0x, h0z⟩ := hGone
  have hsc₀ := apply_sc_eq W (G.one (𝟙 _)) χ₀ hχ₀
  rw [Scheme.IdealSheafData.comap_comp,
    AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_comap_specMap_eq_map χ,
    WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker W (G.one (𝟙 _)) χ₀ hχ₀,
    WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ₀ hsc₀, h0x, h0z, map_zero, map_zero, sub_zero,
    sub_zero, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

end S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span (solution)
