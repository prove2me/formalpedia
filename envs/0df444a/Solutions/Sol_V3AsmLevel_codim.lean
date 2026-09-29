-- Prove2me | solution 1 for V3AsmLevel.codim
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/dc114aa5-b54d-5f64-a44d-1debb3277eea

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_V3Glue_ChartInput_exists_eq_etaG_of_ringKrullDim_le_one
import Theorems.Thm_ModularCurve_DRModelPackageLevel_eq_xi_of_ringKrullDim_stalk_le_one
import Theorems.Thm_AlgebraicGeometry_Scheme_branchIdeal_le_branchIdeal_iff
import Theorems.Thm_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3AsmLevel_codim
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.DRResolvedModelPackageLevelRam.DRResolvedModelChartsLevelRam.etale ModularCurve.DRResolvedModelPackageLevelRam.isIntegral ModularCurve.DRResolvedModelPackageLevelRam.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackageLevelRam.isLocallyNoetherian ModularCurve.DRResolvedModelPackageLevelRam.toDR_proper ModularCurve.DRResolvedModelPackageLevelRam.flat ModularCurve.DRResolvedModelPackageLevelRam.node_deq ModularCurve.DRResolvedModelPackageLevelRam.isProper ModularCurve.DRResolvedModelPackageLevelRam.node_fintype WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicGeometry.graphOver_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qExpandAlgHomC_apply"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.DRResolvedModelPackageLevelRam.DRResolvedModelChartsLevelRam.mk.sizeOf_spec ModularCurve.DRResolvedModelPackageLevelRam.DRResolvedModelChartsLevelRam.mk.injEq ModularCurve.DRResolvedModelPackageLevelRam.mk.injEq ModularCurve.DRResolvedModelPackageLevelRam.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing

namespace E5T3bCodim
namespace Gen

universe u

private theorem eq_of_specializes_of_ringKrullDim_le_one_of_flat {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (r : R) (hr : r ∈ nonZeroDivisors R)
    {a z : X} (h : a ⤳ z) (ha : a ∉ f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens))
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) : a = z := by
  set s : Γ(X, ⊤) := f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) with hs
  have hbs : X.basicOpen s = f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) := by
    rw [hs, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  set g := (X.presheaf.germ ⊤ z trivial).hom s with hg

  have hgP : g ∈ Scheme.branchIdeal h := by
    rw [Scheme.mem_branchIdeal_iff, hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ha (hbs ▸ (X.mem_basicOpen_top s a).mpr hu)

  have hgnzd : g ∈ nonZeroDivisors (X.presheaf.stalk z) := by
    obtain ⟨U, hU, hzU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X))
      (show z ∈ (⊤ : X.Opens) from trivial)
    have hreg := AlgebraicGeometry.map_appTop_mem_nonZeroDivisors_of_flat f r hr U hU
    letI := X.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
    haveI := hU.isLocalization_stalk ⟨z, hzU⟩
    have h1 := IsLocalization.nonZeroDivisors_le_comap (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
      (X.presheaf.stalk z) hreg
    rw [Submonoid.mem_comap] at h1
    have h2 : (X.presheaf.germ U z hzU).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) ∈
        nonZeroDivisors (X.presheaf.stalk z) := h1
    have e1 : (X.presheaf.germ U z hzU).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) = g := by
      rw [hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rw [← e1]
    exact h2

  have hP : Scheme.branchIdeal h = maximalIdeal (X.presheaf.stalk z) := by
    rcases (Order.krullDim_le_one_iff.mp hdim) ⟨Scheme.branchIdeal h, inferInstance⟩ with hmin | hmax
    · exfalso
      have hPmin : Scheme.branchIdeal h ∈ minimalPrimes (X.presheaf.stalk z) := by
        refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
        rintro q ⟨hq, -⟩ hqP
        exact hmin (b := ⟨q, hq⟩) hqP
      exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hPmin) hgP hgnzd
    · have hle : (⟨Scheme.branchIdeal h, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk z)) ≤
          ⟨maximalIdeal _, inferInstance⟩ := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
      exact congrArg PrimeSpectrum.asIdeal (le_antisymm hle (hmax hle))
  have hza : z ⤳ a := by
    rw [← AlgebraicGeometry.Scheme.branchIdeal_le_branchIdeal_iff h (specializes_rfl : z ⤳ z), hP]
    exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  exact (h.antisymm hza).eq

end E5T3bCodim.Gen

namespace E5T3bCodim

open E5T3bCodim.Gen MvPolynomial MvPolynomial.CrossingQuotient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ)

omit [Fact q.Prime] in
include hϖ in
private theorem p_ne_zero : ((q : ℕ) : O) ≠ 0 := fun h =>
  IsDiscreteValuationRing.not_a_field O (by rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl])

private theorem toB_eq_g_toSpec (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) :
    (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).toB n =
      (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).g n ≫ Resolution.toSpec ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) := rfl

local notation "ℭ" => V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H

private theorem hExcMax_of_model
    (hModel : ∀ (e : ℕ) (he : 1 ≤ e) (o : Resolution ((q : ℕ) : O) e),
      (Resolution.toCrossing ((q : ℕ) : O) e).base o =
        Resolution.vertexPt ((q : ℕ) : O) e (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he →
      (∀ o' : Resolution ((q : ℕ) : O) e, o' ⤳ o →
        ((q : ℕ) : O) ∈ ((Resolution.toSpec ((q : ℕ) : O) e).base o').asIdeal → o' = o) →
      ∃ k : Fin (e - 1), o = Resolution.lineUGen ((q : ℕ) : O) e (IsLocalRing.maximalIdeal O)
        (V3AsmLevel.p_mem_maximalIdeal O hϖ) ⟨k, by omega⟩)
    (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (yn : (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Y n),
      (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).q n).base yn).1 = (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n →
      ringKrullDim (((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).Y n).presheaf.stalk yn) ≤ 1 →
      ∃ k, ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).toGlueInput.ιY n).base yn =
        (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).ηG (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H)
          (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ (Sum.inr ⟨n, k⟩) := by
  haveI := H.nodeFinite
  intro n yn hyn h1
  haveI : Flat (((ℭ).toB n : (ℭ).Y n ⟶ Spec (CommRingCat.of O))) := V3Glue.ChartInput.flat_toB (ℭ) n

  have hq : (ℭ).q n yn = (ℭ).xU n := Subtype.ext hyn
  have ho : (ℭ).ρ n ((ℭ).g n yn) = (ℭ).vertex n := by
    rw [← Scheme.Hom.comp_apply, ← V3Glue.ChartInput.q_f (ℭ) n, Scheme.Hom.comp_apply, hq]
    rfl

  have hmaxY : ∀ y' : (ℭ).Y n, y' ⤳ yn →
      y' ∉ ((ℭ).toB n) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → y' = yn :=
    fun y' hy' hV => @eq_of_specializes_of_ringKrullDim_le_one_of_flat _ O _ ((ℭ).toB n)
      (V3Glue.ChartInput.flat_toB (ℭ) n) ((q : ℕ) : O)
      (mem_nonZeroDivisors_of_ne_zero (p_ne_zero (q := q) O hϖ)) _ _ hy' hV h1

  have hmaxR : ∀ o' : (ℭ).Res n, o' ⤳ (ℭ).g n yn →
      ((q : ℕ) : O) ∈ ((Resolution.toSpec ((q : ℕ) : O) ((ℭ).thick n)).base o').asIdeal → o' = (ℭ).g n yn := by
    intro o' ho' hp'
    obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap ((ℭ).g n) ho'
    congr 1
    refine hmaxY y' hy' ?_
    intro hD
    have hD' : ((q : ℕ) : O) ∉ (((ℭ).toB n).base y').asIdeal := hD
    exact hD' hp'

  have hov : (Resolution.toCrossing ((q : ℕ) : O) ((ℭ).thick n)).base ((ℭ).g n yn) =
      Resolution.vertexPt ((q : ℕ) : O) ((ℭ).thick n) (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ)
        ((ℭ).one_le_thick n) := by
    rw [← V3AsmLevel.vertex_eq 𝔛 O ρO κ toκ hϖ H n]
    exact ho
  obtain ⟨k, hk⟩ := hModel ((ℭ).thick n) ((ℭ).one_le_thick n) ((ℭ).g n yn) hov hmaxR
  refine ⟨k, ?_⟩
  rw [V3Glue.ChartInput.ηG_inr, V3Glue.ChartInput.exPt_def]
  congr 1
  exact (ℭ).eq_liftY_of_g_eq n (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H n) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H n k)
    (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H n k) yn hk

private theorem codim_of_model
    (hModel : ∀ (e : ℕ) (he : 1 ≤ e) (o : Resolution ((q : ℕ) : O) e),
      (Resolution.toCrossing ((q : ℕ) : O) e).base o =
        Resolution.vertexPt ((q : ℕ) : O) e (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he →
      (∀ o' : Resolution ((q : ℕ) : O) e, o' ⤳ o →
        ((q : ℕ) : O) ∈ ((Resolution.toSpec ((q : ℕ) : O) e).base o').asIdeal → o' = o) →
      ∃ k : Fin (e - 1), o = Resolution.lineUGen ((q : ℕ) : O) e (IsLocalRing.maximalIdeal O)
        (V3AsmLevel.p_mem_maximalIdeal O hϖ) ⟨k, by omega⟩)
    (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ y : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H), y ∉ (V3AsmLevel.toBase 𝔛 O ρO κ toκ hϖ H) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
      ringKrullDim ((V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).presheaf.stalk y) ≤ 1 → ∃ v, y = V3AsmLevel.η 𝔛 O ρO κ toκ hϖ H hξ v := by
  intro y hy h1
  refine V3Glue.ChartInput.exists_eq_etaG_of_ringKrullDim_le_one (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H)
    (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ (V3AsmLevel.hq 𝔛 O ρO κ toκ hϖ H)
    (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) ?_
    (hExcMax_of_model 𝔛 O ρO hϖ κ toκ H hModel hξ) y hy h1
  intro z _ hzV hz1
  rcases ModularCurve.DRModelPackageLevel.eq_xi_of_ringKrullDim_stalk_le_one
      N₀ q hqN 𝔛 O ρO hϖ κ toκ z hzV hz1 with h | h
  · exact Or.inl (h.trans (V3AsmLevel.ξ_zero 𝔛 O ρO κ toκ).symm)
  · exact Or.inr (h.trans (V3AsmLevel.ξ_one 𝔛 O ρO κ toκ).symm)

end E5T3bCodim

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ y : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H), y ∉ (V3AsmLevel.toBase 𝔛 O ρO κ toκ hϖ H) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) → ringKrullDim ((V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).presheaf.stalk y) ≤ 1 → ∃ v, y = V3AsmLevel.η 𝔛 O ρO κ toκ hϖ H hξ v :=
  E5T3bCodim.codim_of_model 𝔛 O ρO hϖ κ toκ H
    (fun e he o ho hmax => MvPolynomial.CrossingQuotient.Resolution.exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
      ((q : ℕ) : O) e (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he o ho hmax) hξ

#print axioms solution

end S_V3AsmLevel_codim
end P2MW
export P2MW.S_V3AsmLevel_codim (solution)
