-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a693c5aa-afdf-54a4-b2b8-d3073404884b

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_comp_projMap_eq_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassCurve.wIter_zero"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra WeierstrassCurve.DrinfeldGlobal

theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔq : IsUnit (W.map (frobenius T q)).Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    (⟨((𝒢 T W hΔ).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 T W hΔ).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩ := by
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W.toProjective (frobenius T q)
  have hE : (q : Γ(projModelCR W.toProjective, ⊤)) = 0 := by
    have h := congrArg (projModelStrCR W.toProjective).appTop.hom
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero T q))
    rwa [map_natCast, map_zero] at h
  have hΨ := WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
    q T W Φ hΦ hZ hY φ hφ hcoef hE
  exact WeierstrassCurve.DrinfeldGlobal.comp_mul_eq_mul_comp_of_comp_projMap_eq_frobenius
    A 𝒢 h𝒢 h𝒢O q T W hΔ hΔq Φ hΦ φ hφ hcoef hE hΨ t x y

end S_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_mul_eq_mul_comp_of_zChart_pow_originChart_pow (solution)
