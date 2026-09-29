-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.map_algebraMap_localization_atPrime_eq_of_map_originChart_powerSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/64f9211a-f3a0-536b-99a8-8608e721a75a

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_algebraMap_localization_atPrime_eq_of_map_originChart_powerSeries_eq
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW)
    (I J : Ideal (OriginChartRing W)) (h : I.map Φ = J.map Φ) :
    I.map (algebraMap (OriginChartRing W)
      (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))))) =
    J.map (algebraMap (OriginChartRing W)
      (Localization.AtPrime (Ideal.comap Φ (maximalIdeal (PowerSeries T))))) := by
  obtain ⟨ψ, hψ, hff⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_ringHom_localization_atPrime_powerSeries_comp_eq_and_faithfullyFlat
      W Φ hΦsc hΦx hΦz
  refine Ideal.map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat
    (Ideal.comap Φ (maximalIdeal (PowerSeries T))) ψ hff I J ?_
  rw [hψ]
  exact h

end S_WeierstrassCurve_DrinfeldGlobal_map_algebraMap_localization_atPrime_eq_of_map_originChart_powerSeries_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_algebraMap_localization_atPrime_eq_of_map_originChart_powerSeries_eq (solution)
