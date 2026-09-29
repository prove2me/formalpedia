-- Prove2me | solution 1 for PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/65d7e06a-1a78-53aa-95ce-82aeaf2985ba

import Mathlib
import Theorems.Thm_PadicAlgCl_inertiaSubgroupIn_normal
import Theorems.Thm_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
import Theorems.Thm_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_forall_formallyEtale_level_of_forall_inertia_tateModuleRep_eq_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule ExtCitation.LocalLevel.compactGw"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul"
p2m_attr_erase "simp" "HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul PDivisibleGroup.cotangentMap_toCotangent PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent"
p2m_attr_erase "simp" "PDivisibleGroup.baseChange_level PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (f : TateModule p (G.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] ℤ_[p])
    (hf : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ t : PadicAlgCl p, τ t = σ t) →
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ z : TateModule p (G.Points (PadicAlgCl p)),
          f (G.tateModuleRep (PadicAlgCl p) τ z) = f z)
    (x : TateModule p (G.Points (PadicAlgCl p)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (g : G.Point (PadicAlgCl p) w),
      G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
        (x : ℕ → G.Points (PadicAlgCl p)) n ∧
      ∀ a : G.level w, ‖PDivisibleGroup.Point.toAlgHom g a -
        algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) :
    f x = 0 := by
  classical

  let res : (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    { toFun := PadicAlgCl.ringOfIntegers.restrictScalarsRat p K
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  have hres : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (t : PadicAlgCl p), res τ t = τ t := fun τ t => rfl
  haveI hN := PadicAlgCl.inertiaSubgroupIn_normal p
  let I : Subgroup (PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) := ((padicIntegers p).inertiaSubgroupIn ℚ_[p]).comap res
  have hI : I.Normal := Subgroup.Normal.comap hN res

  have hfI : ∀ τ ∈ I, f ∘ₗ G.tateModuleRep (PadicAlgCl p) τ = f := fun τ hτ =>
    LinearMap.ext fun z => hf (res τ) τ (fun t => (hres τ t).symm) hτ z
  obtain ⟨M, -, hMstab, hMI, hMsat, hMker⟩ :=
    LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
      (G.tateModuleRep (PadicAlgCl p)) I hI f hfI

  obtain ⟨h', Q, ψ, Tψ, -, hTψ, hTψτ, hker, hfin⟩ :=
    PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_ker_eq_of_forall_smul_mem_of_ringOfIntegers
      p K G M (fun τ x hx => hMstab τ x hx) hMsat

  have htf1 : ∀ z : TateModule p (Q.Points (PadicAlgCl p)), (p : ℤ_[p]) • z = 0 → z = 0 := by
    intro z hz
    refine Subtype.ext (funext fun n => ?_)
    have h1 := congrArg (fun y : TateModule p (Q.Points (PadicAlgCl p)) => (y : ℕ → Q.Points (PadicAlgCl p)) (n + 1)) hz
    simp only [TateModule.natCast_padicInt_smul_apply, TateModule.coe_zero, Pi.zero_apply] at h1
    rw [TateModule.coe_zero, Pi.zero_apply, ← TateModule.compat z n]
    exact_mod_cast h1
  have htf : ∀ (k : ℕ) (z : TateModule p (Q.Points (PadicAlgCl p))), ((p : ℤ_[p]) ^ k) • z = 0 → z = 0 := by
    intro k
    induction k with
    | zero => intro z hz; rwa [pow_zero, one_smul] at hz
    | succ k ih =>
      intro z hz
      rw [pow_succ', mul_smul] at hz
      exact htf1 z (ih _ (by rwa [smul_comm] at hz))

  have hunr : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
      (∀ t : PadicAlgCl p, τ t = σ t) → σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ z : TateModule p (Q.Points (PadicAlgCl p)), Q.tateModuleRep (PadicAlgCl p) τ z = z := by
    intro σ τ hτσ hσ z
    have hτI : τ ∈ I := by
      change res τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]
      have : res τ = σ := AlgEquiv.ext fun t => (hres τ t).trans (hτσ t)
      rwa [this]
    obtain ⟨k, y, hky⟩ := hfin z
    have hy : Tψ (G.tateModuleRep (PadicAlgCl p) τ y) = Tψ y := by
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hker]
      exact hMI τ hτI y
    have hk : ((p : ℤ_[p]) ^ k) • (Q.tateModuleRep (PadicAlgCl p) τ z - z) = 0 := by
      rw [smul_sub, ← map_smul, hky, ← hTψτ, hy, sub_self]
    exact sub_eq_zero.1 (htf k _ hk)

  have hQet := PDivisibleGroup.forall_formallyEtale_level_of_forall_inertia_tateModuleRep_eq_of_ringOfIntegers p K Q hunr
  have hSx := PDivisibleGroup.forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one
    p K G Q ψ Tψ hTψ x hx
  have hTx : Tψ x = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    obtain ⟨w, g, hg, hgf⟩ := hSx n
    haveI := hQet w
    have hg1 : g = 1 :=
      PDivisibleGroup.point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers p K Q w g hgf
    rw [← hg, hg1, ofMul_one, map_zero, TateModule.coe_zero, Pi.zero_apply]
  have hxM : x ∈ M := by rw [← hker, LinearMap.mem_ker]; exact hTx
  exact hMker x hxM

end S_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers (solution)
