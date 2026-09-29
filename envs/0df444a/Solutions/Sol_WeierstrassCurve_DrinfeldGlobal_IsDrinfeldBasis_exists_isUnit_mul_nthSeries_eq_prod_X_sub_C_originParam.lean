-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/eef5aaf8-6699-5b38-8446-aef437da6c7e

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_map_ideal_comap_ker_eq_ker
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_ker_eq_span_X_sub_C_originParam
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_eq_top_of_not_reducesToOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_torsionIdeal_eq_span_nthSeries
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comap_ker_graphOver_toPullbackId
import Theorems.Thm_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two"
p2m_attr_erase "simp" "MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DivisorAtOAux

theorem prod_fin_divMod {M : Type*} [CommMonoid M] (q : ℕ) (g : ℕ × ℕ → M) :
    ∏ i : Fin (q * q), g (i.val / q, i.val % q) = ∏ ab ∈ Finset.range q ×ˢ Finset.range q, g ab := by
  rw [Fintype.prod_equiv finProdFinEquiv.symm (fun i : Fin (q * q) => g (i.val / q, i.val % q))
    (fun x : Fin q × Fin q => g ((x.1 : ℕ), (x.2 : ℕ))) (fun i => by simp [finProdFinEquiv_symm_apply]),
    Fintype.prod_prod_type, Finset.prod_product]
  rw [← Fin.prod_univ_eq_prod_range (fun a => ∏ b ∈ Finset.range q, g (a, b)) q]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact (Fin.prod_univ_eq_prod_range (fun b => g ((a : ℕ), b)) q)

end DivisorAtOAux

open DivisorAtOAux in
set_option maxHeartbeats 6400000 in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime]
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q)
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ Finset.range q ×ˢ Finset.range q)
    (χ : ℕ × ℕ → (OriginChartRing W →+* T))
    (hχ : ∀ ab ∈ S, ReducesToOrigin (linComb G P Q ab.1 ab.2) (χ ab) (maximalIdeal T))
    (hnS : ∀ ab ∈ Finset.range q ×ˢ Finset.range q, ab ∉ S →
      ∀ χ' : OriginChartRing W →+* T, ¬ ReducesToOrigin (linComb G P Q ab.1 ab.2) χ' (maximalIdeal T)) :
    ∃ u : PowerSeries T, IsUnit u ∧
      u * F.nthSeries q = ∏ ab ∈ S, (PowerSeries.X - PowerSeries.C (originParam (χ ab))) := by
  classical
  obtain ⟨Φ, hΦsc, hΦx, hΦz⟩ := WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries W

  let U : (Spec (CommRingCat.of (OriginChartRing W))).affineOpens := ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
  let e := (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom
  let ρ : (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData → Ideal (PowerSeries T) := fun I =>
    Ideal.map (Φ.comp e) ((I.comap (originChartι W ≫ toPullbackId)).ideal U)
  have hρmul : ∀ I J, ρ (I * J) = ρ I * ρ J := by
    intro I J
    simp only [ρ, Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]
  have hρone : ρ 1 = 1 := by
    simp only [ρ]
    rw [show (1 : (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData) = ⊤ from rfl,
      Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.map_top, Ideal.one_eq_top]
  let ρh : (pullback (projModelStrCR W) (𝟙 (base (T := T)))).IdealSheafData →* Ideal (PowerSeries T) :=
    { toFun := ρ, map_one' := hρone, map_mul' := hρmul }

  have hT : ρ (torsionIdeal G q) = Ideal.span {F.nthSeries q} :=
    WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_torsionIdeal_eq_span_nthSeries W F hFW G hGpts hGone q Φ hΦsc hΦx hΦz

  have hfac : ∀ i : Fin (q * q), ρ ((graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i)).ker) =
      if (i.val / q, i.val % q) ∈ S then Ideal.span {PowerSeries.X - PowerSeries.C (originParam (χ (i.val / q, i.val % q)))}
      else ⊤ := by
    intro i
    have hread : ρ ((graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i)).ker) =
        Ideal.map (Φ.comp e) ((((linComb G P Q (i.val / q) (i.val % q)).1.ker).comap (originChartι W)).ideal U) := by
      simp only [ρ]
      rw [Scheme.IdealSheafData.comap_comp]
      exact congrArg (fun J : (projModelCR W).IdealSheafData => Ideal.map (Φ.comp e) ((J.comap (originChartι W)).ideal U))
        (WeierstrassCurve.DrinfeldGlobal.comap_ker_graphOver_toPullbackId W (linComb G P Q (i.val / q) (i.val % q)))
    have hmem : (i.val / q, i.val % q) ∈ Finset.range q ×ˢ Finset.range q := by
      have hq : 0 < q := (Fact.out : q.Prime).pos
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.div_lt_of_lt_mul i.isLt, Nat.mod_lt _ hq⟩
    rw [hread]
    split_ifs with hin
    · have h := hχ _ hin
      have h1 := WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.map_ideal_comap_ker_eq_ker W _ _ h.1
      have h2 := WeierstrassCurve.DrinfeldGlobal.map_ker_eq_span_X_sub_C_originParam W _ _ h Φ hΦsc hΦx hΦz
      rw [← h2, ← h1, Ideal.map_map]
    · exact WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_ker_eq_top_of_not_reducesToOrigin W _
        (hnS _ hmem hin) Φ hΦsc hΦx hΦz
  have hB : ρ (basisDivisor G q P Q) = Ideal.span {∏ ab ∈ S, (PowerSeries.X - PowerSeries.C (originParam (χ ab)))} := by
    rw [basisDivisor, prodKerGraph_eq_prod, show ρ _ = ρh _ from rfl, map_prod]
    simp only [show ∀ I, ρh I = ρ I from fun _ => rfl, hfac]
    rw [prod_fin_divMod q (fun ab => if ab ∈ S then Ideal.span {PowerSeries.X - PowerSeries.C (originParam (χ ab))} else ⊤),
      ← Ideal.one_eq_top, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hS, Ideal.prod_span_singleton]

  have heq : Ideal.span {F.nthSeries q} = Ideal.span {∏ ab ∈ S, (PowerSeries.X - PowerSeries.C (originParam (χ ab)))} := by
    rw [← hT, ← hB]
    exact congrArg ρ hPQ.symm
  exact PowerSeries.exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq S (fun ab => originParam (χ ab))
    (fun ab hab => (hχ ab hab).2.1) _ heq

end S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam (solution)
