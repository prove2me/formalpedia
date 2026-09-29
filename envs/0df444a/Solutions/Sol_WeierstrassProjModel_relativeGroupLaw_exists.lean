-- Prove2me | solution 1 for WeierstrassProjModel.relativeGroupLaw_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3e95761a-e409-5173-8f3b-8930c1d5783a

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_addMorphism_gluing
import Theorems.Thm_WeierstrassProjModel_relativeGroupLaw_exists_of_gluing
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel in
theorem solution.{u} {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Invertible (2 : R)] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) (hΔ : IsUnit W.Δ) :
    ∃ (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W)
      (G : WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR W.toProjective)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
          (G.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ kw_lrAddMorphism W hcov hcompat houter) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 = t ≫ (kwZeroSect R W).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR W.toProjective)), G.mul t x y = G.mul t y x) := by
  obtain ⟨hcov, hcompat, houter⟩ := WeierstrassProjModel.addMorphism_gluing W hsm hgi hΔ
  obtain ⟨G, hmul, hone, hcomm⟩ :=
    WeierstrassProjModel.relativeGroupLaw_exists_of_gluing W hsm hgi hΔ hcov hcompat houter
  exact ⟨hcov, hcompat, houter, G, hmul, hone, hcomm⟩

end S_WeierstrassProjModel_relativeGroupLaw_exists
end P2MW
export P2MW.S_WeierstrassProjModel_relativeGroupLaw_exists (solution)
