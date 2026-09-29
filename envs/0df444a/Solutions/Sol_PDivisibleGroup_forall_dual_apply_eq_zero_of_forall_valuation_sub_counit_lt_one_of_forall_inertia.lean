-- Prove2me | solution 1 for PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dc9b546f-c3e5-5953-bfd3-c0c430213de7

import Mathlib
import Theorems.Thm_ValuationSubring_exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional
import Theorems.Thm_PDivisibleGroup_exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl
import Theorems.Thm_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule ExtCitation.LocalLevel.compactGw"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul"
p2m_attr_erase "simp" "HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ"
p2m_attr_erase "simp" "PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (hOF : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ F)
    {h : ℕ} (H : PDivisibleGroup O p h)
    (f : TateModule p (H.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] ℤ_[p])
    (hf : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
        (∀ t : AlgebraicClosure ℚ, τ' t = τ t) → τ ∈ P.inertiaSubgroupIn ℚ →
        ∀ z : TateModule p (H.Points (AlgebraicClosure ℚ)),
          f (H.tateModuleRep (AlgebraicClosure ℚ) τ' z) = f z)
    (x : TateModule p (H.Points (AlgebraicClosure ℚ)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (g : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul g) =
        (x : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
      ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom g a -
        algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    f x = 0 := by
  classical

  obtain ⟨K, hK, ι, φ, hφ, hval, hmem, hgal⟩ :=
    ValuationSubring.exists_intermediateField_ringHom_padicAlgCl_of_liesOverPrime_of_finiteDimensional p P hP hOP F hOF
  haveI := hK
  letI : Algebra O (PadicAlgCl.ringOfIntegers p K) := φ.toAlgebra
  obtain ⟨Θ, hΘτ, hΘS⟩ :=
    PDivisibleGroup.exists_linearEquiv_tateModule_baseChange_ringOfIntegers_of_ringHom_padicAlgCl p P K ι
      (fun x => hφ x) hval hmem H
  let fl : TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)) →ₗ[ℤ_[p]] ℤ_[p] := f ∘ₗ (Θ.symm : _ →ₗ[ℤ_[p]] _)
  have hfl : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τl : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
      (∀ t : PadicAlgCl p, τl t = σ t) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ z : TateModule p ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).Points (PadicAlgCl p)), fl ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).tateModuleRep (PadicAlgCl p) τl z) = fl z := by
    intro σ τl hτσ hσ z
    obtain ⟨τ, τ', hττ', hτ, hιτ⟩ := hgal σ τl hτσ hσ
    obtain ⟨y, rfl⟩ : ∃ y, Θ y = z := ⟨Θ.symm z, Θ.apply_symm_apply z⟩
    change f (Θ.symm ((H.baseChange (PadicAlgCl.ringOfIntegers p K)).tateModuleRep (PadicAlgCl p) τl (Θ y))) = f (Θ.symm (Θ y))
    rw [← hΘτ τ' τl hιτ, Θ.symm_apply_apply, Θ.symm_apply_apply]
    exact hf τ τ' hττ' hτ y
  have h0 := PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
    p K (H.baseChange (PadicAlgCl.ringOfIntegers p K)) fl hfl (Θ x) (hΘS x hx)
  change f (Θ.symm (Θ x)) = 0 at h0
  rwa [Θ.symm_apply_apply] at h0

end S_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia
end P2MW
export P2MW.S_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_valuation_sub_counit_lt_one_of_forall_inertia (solution)
