-- Prove2me | solution 1 for V3AsmLevel.edgePt_exhaust
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c53596a4-745b-52e6-ac05-ccd7634ce2af

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_eq_crossingPt_of_mem_closure_of_mem_closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3AsmLevel_edgePt_exhaust
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient ModularCurve Topology

noncomputable section

universe u

private theorem mem_closure_of_isIso_restrict {Res S : Scheme.{u}} (ρ : Res ⟶ S) (Vc : S.Opens) [IsIso (ρ ∣_ Vc)]
    (l o : Res) (hl : ρ.base l ∈ Vc) (ho : ρ.base o ∈ Vc) (h : ρ.base l ⤳ ρ.base o) : o ∈ closure ({l} : Set Res) := by

  let l' : ↥(ρ ⁻¹ᵁ Vc) := ⟨l, hl⟩
  let o' : ↥(ρ ⁻¹ᵁ Vc) := ⟨o, ho⟩

  have himg : (ρ ∣_ Vc).base l' ⤳ (ρ ∣_ Vc).base o' := by
    rw [← (Vc.ι.isOpenEmbedding.isInducing).specializes_iff]
    have e1 : Vc.ι.base ((ρ ∣_ Vc).base l') = ρ.base l := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]; rfl
    have e2 : Vc.ι.base ((ρ ∣_ Vc).base o') = ρ.base o := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]; rfl
    rw [e1, e2]; exact h

  have hemb : IsInducing (ρ ∣_ Vc).base := (Scheme.Hom.isOpenEmbedding (ρ ∣_ Vc)).isInducing
  have h' : l' ⤳ o' := hemb.specializes_iff.mp himg

  have h'' : (ρ ⁻¹ᵁ Vc).ι.base l' ⤳ (ρ ⁻¹ᵁ Vc).ι.base o' := h'.map (ρ ⁻¹ᵁ Vc).ι.base.hom.continuous
  have e3 : (ρ ⁻¹ᵁ Vc).ι.base l' = l := rfl
  have e4 : (ρ ⁻¹ᵁ Vc).ι.base o' = o := rfl
  rw [e3, e4] at h''
  exact specializes_iff_mem_closure.mp h''

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ v w, v ≠ w → ∀ y ∈ ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ v).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)) ∩ ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ w).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)),
      ∃ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n)), y = V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d ∧
        ((v = ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d ∧ w = ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n (d + 1)) ∨ (w = ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d ∧ v = ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n (d + 1))) := by
  intro v w hvw y hy

  have hx : ∀ n, IsClosed ({(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) := fun n => H.hxcl n
  have hinjO : ∀ n, Function.Injective (V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H n) := by
    intro n d d' hdd'
    have hmem : V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H n d ∈
        Set.range (Resolution.ι ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) d').base := by
      rw [hdd']; exact ⟨_, rfl⟩
    exact ((Resolution.origin_mem_range_ι_iff ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) d d').mp hmem).symm
  have hM1 : ∀ n (k k' : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n - 1)) (o : (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n),
      (k : ℕ) < k' →
      o ∈ closure ({V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H n k} : Set ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)) →
      o ∈ closure ({V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H n k'} : Set ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)) →
      (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n o = (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).vertex n →
      ∃ d : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n), (d : ℕ) = k + 1 ∧ (k' : ℕ) = k + 1 ∧
        o = V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H n d := by
    intro n k k' o hkk' ho ho' _
    exact Resolution.exists_eq_origin_of_mem_closure_lineUGen_of_lt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) _ _ o hkk' (by have := k'.2; simp only; omega) ho ho'
  have hM2 : ∀ n (j : Fin 2) (hU : V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n)
      (o o' : (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n),
      (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n o = (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩ →
      o' ∈ closure ({o} : Set ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)) →
      (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n o' = (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).vertex n →
      o' = V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H n ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).dEnd n j) := by
    haveI := H.nodeFinite
    intro n j hU o o' hρo hcl hv
    have he : 1 ≤ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n := (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).one_le_thick n
    have hpm : ((q : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := V3AsmLevel.p_mem_maximalIdeal O hϖ
    have hρo' : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base o = ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩ := hρo

    have hle : (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n ≤ (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).U := (V3AsmLevel.R 𝔛 O ρO κ toκ hϖ H).U_le ((V3AsmLevel.R 𝔛 O ρO κ toκ hϖ H).hnbhd_of H.ET) n
    have hξ0 : (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).U.ι.base (((ModularCurve.DRLevel.XO (N₀ := N₀) ρO).homOfLE hle).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩) = V3AsmLevel.ξ 𝔛 O ρO κ toκ j := by
      change (((ModularCurve.DRLevel.XO (N₀ := N₀) ρO).homOfLE hle ≫ (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).U.ι).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩) = _
      rw [Scheme.homOfLE_ι]
      rfl
    have hfeq : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩ =
        (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).f.base (((ModularCurve.DRLevel.XO (N₀ := N₀) ρO).homOfLE hle).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩) := rfl

    have hne : V3AsmLevel.ξ 𝔛 O ρO κ toκ j ≠ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n := (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).mem_X0 _).mp (hξ j)) n
    have hVc : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩ ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n :=
      ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f_mem_Vc_iff n ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩).mpr hne
    have hVc' := hVc
    change ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, hU⟩ ∈
      PrimeSpectrum.basicOpen (CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) ⊔ PrimeSpectrum.basicOpen (CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) at hVc'

    have hv' : (Resolution.toCrossing ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)).base o' = Resolution.vertexPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he := by
      have h := hv
      rw [V3AsmLevel.vertex_eq] at h
      exact h

    have key : ∀ l : (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n, ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base l ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n → ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base l ⤳ ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base o →
        o' ∈ closure ({l} : Set ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)) := by
      intro l hl hsp
      have hoVc : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base o ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n := by rw [hρo']; exact hVc
      have h1 : o ∈ closure ({l} : Set ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)) :=
        mem_closure_of_isIso_restrict ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n) l o hl hoVc hsp
      exact closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure hcl
    rcases V3Glue.ChartInput.fin_two_eq_zero_or_one j with rfl | rfl
    ·
      have hV : CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU⟩).asIdeal := by
        rw [hfeq]
        apply (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_inf_conv
        rw [hξ0, V3AsmLevel.ξ_zero]
        exact ⟨_, rfl⟩
      have hUn : CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∉ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU⟩).asIdeal := by
        intro hUm
        rcases TopologicalSpace.Opens.mem_sup.mp hVc' with h | h
        · exact (PrimeSpectrum.mem_basicOpen _ _).mp h hUm
        · exact (PrimeSpectrum.mem_basicOpen _ _).mp h hV
      have h𝔪P : ∀ w ∈ IsLocalRing.maximalIdeal O,
          algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) w ∈ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU⟩).asIdeal := by
        intro w hw
        rw [hϖ, Ideal.mem_span_singleton] at hw
        obtain ⟨c, rfl⟩ := hw
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ (Ideal.IsPrime.mem_of_pow_mem inferInstance ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ?_)
        erw [← map_pow, ← CrossingQuotient.U_mul_V]
        exact Ideal.mul_mem_left _ _ hV
      let i0 : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) := ⟨0, he⟩
      have hl : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (Resolution.lineGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0) =
          Resolution.branchVPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he :=
        Resolution.toCrossing_lineGen_zero ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0 rfl
      have hlVc : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (Resolution.lineGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0) ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n := by
        rw [hl]
        change _ ∈ PrimeSpectrum.basicOpen (CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) ⊔
          PrimeSpectrum.basicOpen (CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n))
        exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl
          ((PrimeSpectrum.mem_basicOpen _ _).mpr (U_notMem_lineVIdeal (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _)))
      have hsp : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (Resolution.lineGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0) ⤳ ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base o := by
        rw [hl, hρo']
        exact (PrimeSpectrum.le_iff_specializes _ _).mp ((lineVIdeal_le_iff (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _).mpr ⟨hV, h𝔪P⟩)
      have ho' := key _ hlVc hsp
      rw [Resolution.eq_origin_of_mem_closure_lineGen_zero ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he i0 rfl o' ho' hv']
      change Resolution.origin ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0 = Resolution.origin ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).dEnd n 0)
      exact congrArg _ (Fin.ext (by simp [V3Glue.ChartInput.dEnd_zero, i0]))
    ·
      have hV : CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU⟩).asIdeal := by
        rw [hfeq]
        apply (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_zero_conv
        rw [hξ0, V3AsmLevel.ξ_one]
        exact ⟨_, rfl⟩
      have hUn : CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∉ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU⟩).asIdeal := by
        intro hUm
        rcases TopologicalSpace.Opens.mem_sup.mp hVc' with h | h
        · exact (PrimeSpectrum.mem_basicOpen _ _).mp h hV
        · exact (PrimeSpectrum.mem_basicOpen _ _).mp h hUm
      have h𝔪P : ∀ w ∈ IsLocalRing.maximalIdeal O,
          algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) w ∈ (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU⟩).asIdeal := by
        intro w hw
        rw [hϖ, Ideal.mem_span_singleton] at hw
        obtain ⟨c, rfl⟩ := hw
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ (Ideal.IsPrime.mem_of_pow_mem inferInstance ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ?_)
        erw [← map_pow, ← CrossingQuotient.U_mul_V]
        exact Ideal.mul_mem_right _ _ hV
      let i0 : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) := ⟨(V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n - 1, by omega⟩
      have hl : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (Resolution.lineUGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0) =
          Resolution.branchUPt ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he :=
        Resolution.toCrossing_lineUGen_last ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0 (Nat.sub_add_cancel he)
      have hlVc : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (Resolution.lineUGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0) ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Vc n := by
        rw [hl]
        change _ ∈ PrimeSpectrum.basicOpen (CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) ⊔
          PrimeSpectrum.basicOpen (CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n))
        exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr
          ((PrimeSpectrum.mem_basicOpen _ _).mpr (V_notMem_lineUIdeal (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _)))
      have hsp : ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base (Resolution.lineUGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0) ⤳ ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ρ n).base o := by
        rw [hl, hρo']
        exact (PrimeSpectrum.le_iff_specializes _ _).mp ((lineUIdeal_le_iff (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _).mpr ⟨hV, h𝔪P⟩)
      have ho' := key _ hlVc hsp
      rw [Resolution.eq_origin_of_mem_closure_lineUGen_last ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he i0 (Nat.sub_add_cancel he) o' ho' hv']
      change Resolution.origin ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm i0 = Resolution.origin ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).dEnd n 1)
      exact congrArg _ (Fin.ext (by simp [V3Glue.ChartInput.dEnd_one, i0]))
  have hM3 : ∀ n (d : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) (k : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n - 1)),
      V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H n d ∈
        closure ({V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H n k} : Set ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Res n)) →
      (d : ℕ) = k ∨ (d : ℕ) = k + 1 := by
    intro n d k h
    exact Resolution.eq_or_eq_of_origin_mem_closure_lineUGen ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) d _ (by have := k.2; simp only; omega) h
  have hW0 : ∀ x : ModularCurve.DRLevel.XO (N₀ := N₀) ρO, x ∈ closure ({V3AsmLevel.ξ 𝔛 O ρO κ toκ 0} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) →
      x ∈ closure ({V3AsmLevel.ξ 𝔛 O ρO κ toκ 1} : Set (ModularCurve.DRLevel.XO (N₀ := N₀) ρO)) → x ∉ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0 := by

    intro x h0 h1 hx0
    haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
    rw [V3AsmLevel.ξ_zero] at h0
    rw [V3AsmLevel.ξ_one] at h1
    have h0' : x ∈ closure (Set.range ⇑(𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base) :=
      closure_mono (Set.singleton_subset_iff.mpr
        (Set.mem_range_self (f := ⇑(𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base) (genericPoint ↥(ModularCurve.DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))) h0
    have h1' : x ∈ closure (Set.range ⇑(𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base) :=
      closure_mono (Set.singleton_subset_iff.mpr
        (Set.mem_range_self (f := ⇑(𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base) (genericPoint ↥(ModularCurve.DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))))) h1
    obtain ⟨m, rfl⟩ := ModularCurve.DRModelPackageLevel.exists_eq_crossingPt_of_mem_closure_of_mem_closure
      N₀ q hqN 𝔛 O ρO hϖ κ toκ x h0' h1'
    exact ((V3AsmLevel.mem_X0_iff 𝔛 O ρO κ toκ hϖ H _).mp hx0) m rfl

  obtain ⟨n, d, hyd, hvw'⟩ := (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).edgePt'_exhaust (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ
    (V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hoRes 𝔛 O ρO κ toκ hϖ H) hx hinjO hM1 hM2 hM3 hW0 v w hvw y
    (by first | exact hy | simpa only [V3AsmLevel.comp_def] using hy | (simp only [V3AsmLevel.comp_def] at hy ⊢; exact hy))
  refine ⟨n, d, ?_, ?_⟩
  · rw [hyd, V3AsmLevel.edgePt_def]
  · first | exact hvw' | simpa only [V3AsmLevel.chainPos'_eq] using hvw' | (simp only [V3AsmLevel.chainPos'_eq] at hvw' ⊢; exact hvw')

end

end S_V3AsmLevel_edgePt_exhaust
end P2MW
export P2MW.S_V3AsmLevel_edgePt_exhaust (solution)
