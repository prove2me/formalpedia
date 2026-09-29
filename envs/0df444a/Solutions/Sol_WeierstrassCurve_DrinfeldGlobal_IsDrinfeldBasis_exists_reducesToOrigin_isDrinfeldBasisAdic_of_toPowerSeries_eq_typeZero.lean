-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b728ab64-871a-5da4-9a49-1454448e5fcc

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
import Theorems.Thm_WeierstrassCurve_exists_isUnit_map_residue_nthSeries_eq_mul_X_pow_of_isDrinfeldBasisAdic_zero
import Theorems.Thm_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two"
p2m_attr_erase "simp" "MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BridgeAux

theorem drinfeldDivisorAdic_eq {T : Type} [CommRing T] (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    F.drinfeldDivisorAdic I q x₀ x₁ =
      ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (F.linCombAdic I x₀ x₁ a b)) :=
  rfl

theorem linComb_one_zero {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) : linComb G P Q 1 0 = P := by
  simp [linComb, RelativeGroupLaw.nsmul_one_apply, RelativeGroupLaw.nsmul_zero, G.mul_one, G.one_mul]

theorem linComb_zero_one {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (P Q : Section W) : linComb G P Q 0 1 = Q := by
  simp [linComb, RelativeGroupLaw.nsmul_one_apply, RelativeGroupLaw.nsmul_zero, G.one_mul, G.mul_one]

end BridgeAux

open BridgeAux in
set_option maxHeartbeats 3200000 in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) [Fact q.Prime]
    (hss : (W.map (residue T)).formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (P Q : Section W) (hPQ : IsDrinfeldBasis G q P Q) :
    ∃ (χP χQ : OriginChartRing W →+* T),
      ReducesToOrigin P χP (maximalIdeal T) ∧ ReducesToOrigin Q χQ (maximalIdeal T) ∧
      F.IsDrinfeldBasisAdic (maximalIdeal T) q (originParam χP) (originParam χQ) := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  let good : ℕ × ℕ → Prop := fun ab =>
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin (linComb G P Q ab.1 ab.2) χ (maximalIdeal T)
  let S : Finset (ℕ × ℕ) := (Finset.range q ×ˢ Finset.range q).filter good
  let χ : ℕ × ℕ → (OriginChartRing W →+* T) := fun ab =>
    if h : good ab then h.choose else hGone.choose
  have hχ : ∀ ab ∈ S, ReducesToOrigin (linComb G P Q ab.1 ab.2) (χ ab) (maximalIdeal T) := by
    intro ab hab
    have hg : good ab := (Finset.mem_filter.mp hab).2
    simp only [χ, dif_pos hg]
    exact hg.choose_spec
  have hS : S ⊆ (Finset.range q ×ˢ Finset.range q) := Finset.filter_subset _ _
  have hnS : ∀ ab ∈ (Finset.range q ×ˢ Finset.range q), ab ∉ S →
      ∀ χ' : OriginChartRing W →+* T, ¬ ReducesToOrigin (linComb G P Q ab.1 ab.2) χ' (maximalIdeal T) := by
    intro ab hab hnot χ' hred
    exact hnot (Finset.mem_filter.mpr ⟨hab, ⟨χ', hred⟩⟩)

  obtain ⟨u, hu, hprod⟩ :=
    WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.exists_isUnit_mul_nthSeries_eq_prod_X_sub_C_originParam
      W F hFW G hGpts hGone q P Q hPQ S hS χ hχ hnS

  have hmap := WeierstrassCurve.exists_isUnit_map_residue_nthSeries_eq_mul_X_pow_of_isDrinfeldBasisAdic_zero
    W F hFW q hss
  have hcard : S.card = q * q :=
    PowerSeries.card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow S
      (fun ab => originParam (χ ab)) (fun ab hab => (hχ ab hab).2.1) (F.nthSeries q) u hu (q * q) hmap hprod
  have hSeq : S = (Finset.range q ×ˢ Finset.range q) := by
    apply Finset.eq_of_subset_of_card_le hS
    rw [hcard, Finset.card_product, Finset.card_range]
  have hall : ∀ ab ∈ (Finset.range q ×ˢ Finset.range q), ReducesToOrigin (linComb G P Q ab.1 ab.2) (χ ab) (maximalIdeal T) := by
    intro ab hab; exact hχ ab (hSeq ▸ hab)

  have h10 : ((1, 0) : ℕ × ℕ) ∈ (Finset.range q ×ˢ Finset.range q) := by simp [Finset.mem_product]; omega
  have h01 : ((0, 1) : ℕ × ℕ) ∈ (Finset.range q ×ˢ Finset.range q) := by simp [Finset.mem_product]; omega
  have hP : ReducesToOrigin P (χ (1, 0)) (maximalIdeal T) := by
    have := hall (1, 0) h10; rwa [linComb_one_zero] at this
  have hQ : ReducesToOrigin Q (χ (0, 1)) (maximalIdeal T) := by
    have := hall (0, 1) h01; rwa [linComb_zero_one] at this
  refine ⟨χ (1, 0), χ (0, 1), hP, hQ, ?_⟩

  have hpar : ∀ ab ∈ (Finset.range q ×ˢ Finset.range q), originParam (χ ab) =
      F.linCombAdic (maximalIdeal T) (originParam (χ (1, 0))) (originParam (χ (0, 1))) ab.1 ab.2 := by
    intro ab hab
    obtain ⟨χ', hχ', hz'⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_linComb_and_originParam_eq_linCombAdic
        W F hFW G hGpts hGone P Q (χ (1, 0)) (χ (0, 1)) hP hQ ab.1 ab.2
    have heq : χ' = χ ab := WeierstrassCurve.DrinfeldGlobal.IsOriginChartSection.eq hχ'.1 (hall ab hab).1
    rw [← heq, hz']

  have hdiv : F.drinfeldDivisorAdic (maximalIdeal T) q (originParam (χ (1, 0))) (originParam (χ (0, 1))) =
      ∏ ab ∈ S, (PowerSeries.X - PowerSeries.C (originParam (χ ab))) := by
    rw [drinfeldDivisorAdic_eq, ← Finset.prod_product', ← hSeq]
    exact Finset.prod_congr rfl (fun ab hab => by rw [hpar ab (hS hab)])
  refine (F.isDrinfeldBasisAdic_iff _ _ _ _).mpr ⟨↑hu.unit⁻¹, Units.isUnit _, ?_⟩
  rw [hdiv, ← hprod, ← mul_assoc, IsUnit.val_inv_mul, one_mul]

end S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_exists_reducesToOrigin_isDrinfeldBasisAdic_of_toPowerSeries_eq_typeZero (solution)
