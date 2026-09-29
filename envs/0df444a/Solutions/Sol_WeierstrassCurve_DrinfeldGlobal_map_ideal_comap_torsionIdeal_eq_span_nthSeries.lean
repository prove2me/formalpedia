-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_torsionIdeal_eq_span_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/043c4596-ab3f-549a-ba3f-c992960eb040

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdeal_eq_comap_ker_one
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_one_eq_span
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_ideal_comap_specMap_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_torsionIdeal_eq_span_nthSeries
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsCommFormalGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one"
p2m_attr_erase "simp" "MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    Ideal.map (Φ.comp (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom)
      (((torsionIdeal G q).comap (originChartι W ≫ toPullbackId)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      Ideal.span {F.nthSeries q} := by
  obtain ⟨χq, hχsc, hcomp, hχx, hχz⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart W F hFW G hGpts hGone q Φ
      hΦsc hΦx hΦz

  rw [← Ideal.map_map, ← AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_comap_specMap_eq_map Φ,
    ← Scheme.IdealSheafData.comap_comp, ← Category.assoc,
    WeierstrassCurve.DrinfeldGlobal.comap_torsionIdeal_eq_comap_ker_one W G q, Category.assoc, hcomp,
    WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_ker_one_eq_span W G hGone χq, hχx, hχz]

  have hs0 : PowerSeries.constantCoeff (F.nthSeries q) = 0 := F.constantCoeff_nthSeries q
  have ha : PowerSeries.HasSubst (F.nthSeries q) := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have hdvd : F.nthSeries q ∣ PowerSeries.subst (F.nthSeries q) W.formalW := by
    obtain ⟨g, hg⟩ := (PowerSeries.X_dvd_iff).mpr W.constantCoeff_formalW
    refine ⟨PowerSeries.subst (F.nthSeries q) g, ?_⟩
    rw [hg, PowerSeries.subst_mul ha, PowerSeries.subst_X ha]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f hf
    rcases hf with rfl | rfl
    · exact (Ideal.neg_mem_iff _).mpr (Ideal.subset_span rfl)
    · exact (Ideal.neg_mem_iff _).mpr (Ideal.mem_span_singleton.mpr hdvd)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h : -F.nthSeries q ∈ Ideal.span ({-F.nthSeries q, -PowerSeries.subst (F.nthSeries q) W.formalW} :
        Set (PowerSeries T)) := Ideal.subset_span (Set.mem_insert _ _)
    rwa [Ideal.neg_mem_iff] at h

end S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_torsionIdeal_eq_span_nthSeries
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_torsionIdeal_eq_span_nthSeries (solution)
