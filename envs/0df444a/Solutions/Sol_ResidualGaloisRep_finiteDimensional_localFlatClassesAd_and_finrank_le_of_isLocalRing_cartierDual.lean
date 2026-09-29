-- Prove2me | solution 1 for ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4ff1a64a-ab2b-5549-8586-f755f70c2d7a

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt
import Theorems.Thm_ResidualGaloisRep_exists_hondaSystem_finrank_endHonda_le_injective_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_HondaSystem_finrank_selfExt_le_finrank_endHonda_add_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid"
p2m_attr_erase "instance" "MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal Deformation.HondaSystem.SplitCoordinates.instHopfGc Deformation.HondaSystem.SplitCoordinates.instCommRingGe Deformation.HondaSystem.SplitCoordinates.instCommRingGc Deformation.HondaSystem.SplitCoordinates.instCommRingEt Deformation.HondaSystem.SplitCoordinates.instHopfGe Deformation.HondaSystem.SplitCoordinates.instHopfEt Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem instTopologicallyFGOfFiniteType ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff HopfOrder.doubleCmp_tmul"
p2m_attr_erase "simp" "HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto Deformation.HondaSystem.SplitCoordinates.mk.sizeOf_spec Deformation.HondaSystem.SplitCoordinates.mk.injEq Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply"
p2m_attr_erase "simp" "Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.PLoc.map_algebraMap Deformation.PLoc.map_invPow Deformation.UnipotentWittCovector.wUp_of Deformation.UnipotentWittCovector.wHom_apply Deformation.UnipotentWittCovector.wLevel_succ_truncate Deformation.PLoc.mapLinear_apply ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hunip : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f)) :
    FiniteDimensional k (ρbar.localFlatClassesAd p) ∧
      Module.finrank k (ρbar.localFlatClassesAd p) ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants + 1 := by
  classical
  obtain ⟨D, _, _, _, 𝓗, hD2, hEnd, f, hf⟩ :=
    ResidualGaloisRep.exists_hondaSystem_finrank_endHonda_le_injective_of_isLocalRing_cartierDual
      p hp2 hker ρbar hunip
  have hExt := Deformation.HondaSystem.finrank_selfExt_le_finrank_endHonda_add_one rfl 𝓗 hD2
  haveI : Module.Finite k 𝓗.selfExt :=
    inferInstanceAs (Module.Finite k (↥𝓗.extPairs ⧸ (𝓗.innerPairs.comap 𝓗.extPairs.subtype)))
  haveI : FiniteDimensional k (ρbar.localFlatClassesAd p) := Module.Finite.of_injective f hf
  refine ⟨inferInstance, ?_⟩
  have h1 : Module.finrank k (ρbar.localFlatClassesAd p) ≤ Module.finrank k 𝓗.selfExt :=
    LinearMap.finrank_le_finrank_of_injective hf
  omega

end S_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_cartierDual (solution)
