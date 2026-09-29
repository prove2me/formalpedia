-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/45a1758b-546e-5ca0-96fa-bde2bda13172

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_comap_ker_originChartInclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hP : IsOriginChartSection P χ) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
      (((Scheme.Hom.ker P.1).comap (originChartι W)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      RingHom.ker χ := by
  rw [WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.comap_ker_originChartInclusion W P χ hP,
    Scheme.Hom.ker_apply]
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.toRingHom.comp
        ((Spec.map (CommRingCat.ofHom χ)).app ⊤).hom =
      χ.comp (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom := by
    have h2 := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
    exact h2
  have hker : RingHom.ker ((Spec.map (CommRingCat.ofHom χ)).app ⊤).hom =
      (RingHom.ker χ).comap (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
    have hx := RingHom.congr_fun hnat x
    simp only [RingHom.comp_apply] at hx
    rw [← hx]
    exact (map_eq_zero_iff _ (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.injective).symm
  rw [hker]
  exact Ideal.map_comap_of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).commRingCatIsoToRingEquiv.surjective _

end S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker (solution)
