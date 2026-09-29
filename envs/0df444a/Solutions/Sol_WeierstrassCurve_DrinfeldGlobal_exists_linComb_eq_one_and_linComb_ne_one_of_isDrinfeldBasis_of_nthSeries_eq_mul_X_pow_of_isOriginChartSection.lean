-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/893ff651-4813-5b04-ae96-09417fb8a423

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_card_eq_of_nthSeries_eq_mul_X_pow
import Theorems.Thm_Finset_exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection
p2m_attr_erase "instance" "WeierstrassCurve.instIsCommFormalGroup WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one"
p2m_attr_erase "simp" "MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {k : Type} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (G : RelativeGroupLaw k (projModelStrCR W))
    (hG : ∃ ev, IsPointsEval W G ev)

    (hGO : ∃ χ : OriginChartRing W →+* k,
      IsOriginChartSection (G.one (𝟙 (base (T := k)))) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)

    (F : FormalGroup k) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (hord : ∃ u : PowerSeries k, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    ∃ a b c d : ℕ, IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q) ∧
      linComb G P Q a b = G.one (𝟙 (base (T := k))) ∧
      linComb G P Q c d ≠ G.one (𝟙 (base (T := k))) := by
  classical
  obtain ⟨S, hS, hcard⟩ :=
    WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_card_eq_of_nthSeries_eq_mul_X_pow
      q W G hG hGO F hFW hord P Q hPQ
  have hsub : S ⊆ Finset.range q ×ˢ Finset.range q := by
    intro ab hab
    obtain ⟨h1, h2, -⟩ := (hS ab).1 hab
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 h1, Finset.mem_range.2 h2⟩
  obtain ⟨a, b, c, d, hab, hc, hd, hcd, hunit⟩ :=
    Finset.exists_mem_and_not_mem_and_isUnit_sub_mul_of_card_eq_of_prime q S hsub hcard
  exact ⟨a, b, c, d, hunit, ((hS (a, b)).1 hab).2.2, fun h => hcd ((hS (c, d)).2 ⟨hc, hd, h⟩)⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_linComb_eq_one_and_linComb_ne_one_of_isDrinfeldBasis_of_nthSeries_eq_mul_X_pow_of_isOriginChartSection (solution)
