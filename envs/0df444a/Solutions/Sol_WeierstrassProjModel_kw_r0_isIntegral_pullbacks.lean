-- Prove2me | solution 1 for WeierstrassProjModel.kw_r0_isIntegral_pullbacks
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/04d4a142-5659-5b1a-8033-06230f90e5d5

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_r0_isIntegral_pullbacks

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem solution {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R)
    (hsm : Smooth (projModelStrCR W.toProjective))
    (hgi : GeometricallyIntegral (projModelStrCR W.toProjective)) :
    IsIntegral (projModelCR W.toProjective) ∧
    IsIntegral ↑(pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)) ∧
    IsIntegral ↑(pullback
      (pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ≫
        projModelStrCR W.toProjective)
      (projModelStrCR W.toProjective)) := by
  set q := projModelStrCR W.toProjective with hq
  haveI := hsm; haveI := hgi
  haveI hE : IsIntegral (projModelCR W.toProjective) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian q
  haveI : IsLocallyNoetherian (projModelCR W.toProjective) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  haveI hE2 : IsIntegral ↑(pullback q q) := by
    haveI : GeometricallyIntegral (pullback.fst q q) :=
      MorphismProperty.pullback_fst _ _ hgi
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst q q)
  haveI : IsLocallyNoetherian ↑(pullback q q) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst q q)
  haveI hE3 : IsIntegral ↑(pullback (pullback.fst q q ≫ q) q) := by
    haveI : GeometricallyIntegral (pullback.fst (pullback.fst q q ≫ q) q) :=
      MorphismProperty.pullback_fst _ _ hgi
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
      (pullback.fst (pullback.fst q q ≫ q) q)
  exact ⟨hE, hE2, hE3⟩

end S_WeierstrassProjModel_kw_r0_isIntegral_pullbacks
end P2MW
export P2MW.S_WeierstrassProjModel_kw_r0_isIntegral_pullbacks (solution)
