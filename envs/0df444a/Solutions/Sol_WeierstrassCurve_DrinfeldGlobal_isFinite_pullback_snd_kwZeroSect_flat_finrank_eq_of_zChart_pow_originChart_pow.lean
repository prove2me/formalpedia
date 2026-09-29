-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/843832a1-33e8-5ec7-a86d-8c8fb3c64910

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringEquiv_originChartRing_quotient_span_xOverY_pow_zOverY_pow_adjoinRoot_X_pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow_of_ringEquiv_adjoinRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow
p2m_attr_erase "simp" "WeierstrassCurve.wIter_zero MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory.Limits in

theorem solution
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective) :
    IsFinite (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧ Flat (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      LocallyOfFinitePresentation (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      ∀ s, (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1).finrank s = q := by
  obtain halg := WeierstrassCurve.DrinfeldGlobal.exists_ringEquiv_originChartRing_quotient_span_xOverY_pow_zOverY_pow_adjoinRoot_X_pow q T W
  exact WeierstrassCurve.DrinfeldGlobal.isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow_of_ringEquiv_adjoinRoot
    q T W Φ hΦ hZ hY halg

end S_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow (solution)
