-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_card_eq_of_nthSeries_eq_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0a10a197-4c45-5209-afd8-cabe1905b9ff

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_card_eq_of_nthSeries_eq_mul_X_pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two"
p2m_attr_erase "simp" "MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {k : Type} [Field k] (q : ℕ) [Fact q.Prime]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (G : RelativeGroupLaw k (projModelStrCR W))
    (hG : ∃ ev, IsPointsEval W G ev)
    (hGO : ∃ χ : OriginChartRing W →+* k,
      IsOriginChartSection (G.one (𝟙 (base (T := k)))) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (F : FormalGroup k) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (hord : ∃ u : PowerSeries k, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    ∃ S : Finset (ℕ × ℕ),
      (∀ ab : ℕ × ℕ, ab ∈ S ↔ ab.1 < q ∧ ab.2 < q ∧ linComb G P Q ab.1 ab.2 = G.one (𝟙 (base (T := k)))) ∧
      S.card = q := by
  classical

  have hm : maximalIdeal k = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField k)
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [hm]; infer_instance
  obtain ⟨χ₀, hχ₀, hx0, hz0⟩ := hGO
  have hpar0 : originParam χ₀ = 0 := by simp [originParam, hx0]
  have hred0 : ReducesToOrigin (G.one (𝟙 (base (T := k)))) χ₀ (maximalIdeal k) := by
    refine ⟨hχ₀, ?_, ?_⟩
    · simp [originParam, hx0]
    · simp [originW, hz0]

  let S : Finset (ℕ × ℕ) := (Finset.range q ×ˢ Finset.range q).filter
    (fun ab => linComb G P Q ab.1 ab.2 = G.one (𝟙 (base (T := k))))
  have hSmem : ∀ ab : ℕ × ℕ, ab ∈ S ↔
      ab.1 < q ∧ ab.2 < q ∧ linComb G P Q ab.1 ab.2 = G.one (𝟙 (base (T := k))) := by
    intro ab
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]
  have hS : S ⊆ Finset.range q ×ˢ Finset.range q := Finset.filter_subset _ _
  refine ⟨S, hSmem, ?_⟩

  have hχ : ∀ ab ∈ S, ReducesToOrigin (linComb G P Q ab.1 ab.2) ((fun _ => χ₀) ab) (maximalIdeal k) := by
    intro ab hab
    rw [((hSmem ab).mp hab).2.2]
    exact hred0
  have hnS : ∀ ab ∈ Finset.range q ×ˢ Finset.range q, ab ∉ S →
      ∀ χ' : OriginChartRing W →+* k, ¬ ReducesToOrigin (linComb G P Q ab.1 ab.2) χ' (maximalIdeal k) := by
    intro ab hab habS χ' hred
    apply habS
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    refine (hSmem ab).mpr ⟨hab.1, hab.2, ?_⟩
    have hpar : originParam χ' = originParam χ₀ := by
      obtain ⟨-, h1, -⟩ := hred
      rw [hm, Ideal.mem_bot] at h1
      rw [h1, hpar0]
    exact (WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq
      W _ _ χ' χ₀ hred hred0 hpar).1
  obtain ⟨u, hu, hprod⟩ :=
    WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
      W F hFW G hG ⟨χ₀, hχ₀, hx0, hz0⟩ q P Q hPQ S hS (fun _ => χ₀) hχ hnS
  simp only [hpar0, map_zero, sub_zero, Finset.prod_const] at hprod

  obtain ⟨u', hu', hq'⟩ := hord
  rw [hq', ← mul_assoc] at hprod
  by_contra hne
  have h1 := congrArg (fun p : PowerSeries k => PowerSeries.coeff q p) hprod
  simp only [PowerSeries.coeff_X_pow, if_neg (fun h : q = S.card => hne h.symm)] at h1
  have h2 : PowerSeries.coeff q ((u * u') * PowerSeries.X ^ q) = PowerSeries.coeff 0 (u * u') := by
    simpa using PowerSeries.coeff_mul_X_pow (u * u') q 0
  rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
  have h3 : IsUnit (PowerSeries.constantCoeff (u * u')) := PowerSeries.isUnit_constantCoeff _ (hu.mul hu')
  rw [h1] at h3
  exact not_isUnit_zero h3

end S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_card_eq_of_nthSeries_eq_mul_X_pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_card_eq_of_nthSeries_eq_mul_X_pow (solution)
