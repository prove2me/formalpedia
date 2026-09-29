-- Prove2me | solution 1 for ResidualGaloisRep.finrank_endHonda_le_finrank_invariants_of_hondaSystem_model
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0007b72b-e8b1-5373-abfd-cc29c76d6566

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_HondaSelfExt
import Theorems.Thm_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_finrank_endHonda_le_finrank_invariants_of_hondaSystem_model
p2m_attr_erase "instance" "PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing"
p2m_attr_erase "instance" "Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal Deformation.HondaSystem.SplitCoordinates.instHopfGc Deformation.HondaSystem.SplitCoordinates.instCommRingGe Deformation.HondaSystem.SplitCoordinates.instCommRingGc Deformation.HondaSystem.SplitCoordinates.instCommRingEt Deformation.HondaSystem.SplitCoordinates.instHopfGe Deformation.HondaSystem.SplitCoordinates.instHopfEt Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem instTopologicallyFGOfFiniteType CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule"
p2m_attr_erase "simp" "PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast ModpDieudonneRealization.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero"
p2m_attr_erase "simp" "PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto Deformation.HondaSystem.SplitCoordinates.mk.sizeOf_spec Deformation.HondaSystem.SplitCoordinates.mk.injEq Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.PLoc.map_algebraMap Deformation.PLoc.map_invPow Deformation.UnipotentWittCovector.wUp_of Deformation.UnipotentWittCovector.wHom_apply Deformation.UnipotentWittCovector.wLevel_succ_truncate"
p2m_attr_erase "simp" "Deformation.PLoc.mapLinear_apply HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt TensorProduct

namespace P2mEndHondaBound

theorem finrank_le_of_injective {k : Type} [Field k] [Finite k] {M N : Type*} [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] [Module.Finite k M] [Module.Finite k N] (f : M → N)
    (hf : Function.Injective f) : Module.finrank k M ≤ Module.finrank k N := by
  haveI : Finite M := Module.finite_of_finite k
  haveI : Finite N := Module.finite_of_finite k
  have h := Nat.card_le_card_of_injective f hf
  rw [Module.natCard_eq_pow_finrank (K := k) (V := M),
    Module.natCard_eq_pow_finrank (K := k) (V := N)] at h
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).1 h

section Galois

variable (p : ℕ) [Fact p.Prime]

noncomputable def toLoc :
    (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ≃* primeLocalGaloisGroup (pPrime p) :=
  MulEquiv.refl _

theorem localAut_toLoc (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ResidualGaloisRep.localAut p (toLoc p σ) = σ := rfl

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k)

local notation "ιp" => primeLocalToGlobal (pPrime p)

@[reducible] noncomputable def galAction : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ρbar.V where
  smul σ v := ρbar.ρ (ιp (toLoc p σ)) v
  one_smul v := by
    show ρbar.ρ (ιp (toLoc p 1)) v = v
    rw [map_one, map_one, map_one]
    rfl
  mul_smul σ τ v := by
    show ρbar.ρ (ιp (toLoc p (σ * τ))) v = ρbar.ρ (ιp (toLoc p σ)) (ρbar.ρ (ιp (toLoc p τ)) v)
    rw [map_mul, map_mul, map_mul]
    rfl
  smul_zero σ := map_zero _
  smul_add σ v w := map_add _ _ _

theorem galAction_smul (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (v : ρbar.V) :
    (letI := galAction p ρbar; σ • v) = ρbar.ρ (ιp (toLoc p σ)) v := rfl

end Galois

section Points

variable (p : ℕ) [Fact p.Prime]
variable (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁]

abbrev Pts : Type := WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)

noncomputable def precomp (g : H₁ →ₐc[ℤ_[p]] H₁) (f : Pts p H₁) : Pts p H₁ :=
  WithConv.toConv ((WithConv.ofConv f).comp (g : H₁ →ₐ[ℤ_[p]] H₁))

theorem precomp_mul (g : H₁ →ₐc[ℤ_[p]] H₁) (f f' : Pts p H₁) :
    precomp p H₁ g (f * f') = precomp p H₁ g f * precomp p H₁ g f' := by
  apply WithConv.ext
  simp only [precomp, WithConv.ofConv_toConv]
  exact AlgHom.convMul_comp_bialgHom_distrib f f' g

theorem precomp_comp (g g' : H₁ →ₐc[ℤ_[p]] H₁) (f : Pts p H₁) :
    precomp p H₁ (g.comp g') f = precomp p H₁ g' (precomp p H₁ g f) :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

noncomputable def galComp (σ : primeLocalGaloisGroup (pPrime p)) (f : Pts p H₁) : Pts p H₁ :=
  WithConv.toConv
    (((ResidualGaloisRep.localAut p σ).toAlgHom.restrictScalars ℤ_[p]).comp (WithConv.ofConv f))

theorem galComp_apply (σ : primeLocalGaloisGroup (pPrime p)) (f : Pts p H₁) (h : H₁) :
    galComp p H₁ σ f h = ResidualGaloisRep.localAut p σ (f h) := rfl

theorem precomp_galComp (g : H₁ →ₐc[ℤ_[p]] H₁) (σ : primeLocalGaloisGroup (pPrime p))
    (f : Pts p H₁) : precomp p H₁ g (galComp p H₁ σ f) = galComp p H₁ σ (precomp p H₁ g f) :=
  WithConv.ext (AlgHom.ext fun _ => rfl)

variable {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (e₁ : Pts p H₁ ≃ ρbar.V)

noncomputable def ptsEnd (g : H₁ →ₐc[ℤ_[p]] H₁) (v : ρbar.V) : ρbar.V :=
  e₁ (precomp p H₁ g (e₁.symm v))

theorem ptsEnd_apply_e₁ (g : H₁ →ₐc[ℤ_[p]] H₁) (f : Pts p H₁) :
    ptsEnd p H₁ ρbar e₁ g (e₁ f) = e₁ (precomp p H₁ g f) := by
  simp [ptsEnd]

theorem ptsEnd_add (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g) (g : H₁ →ₐc[ℤ_[p]] H₁)
    (v w : ρbar.V) :
    ptsEnd p H₁ ρbar e₁ g (v + w) = ptsEnd p H₁ ρbar e₁ g v + ptsEnd p H₁ ρbar e₁ g w := by
  obtain ⟨f, rfl⟩ := e₁.surjective v
  obtain ⟨f', rfl⟩ := e₁.surjective w
  rw [← he₁_add, ptsEnd_apply_e₁, ptsEnd_apply_e₁, ptsEnd_apply_e₁, precomp_mul, he₁_add]

theorem ptsEnd_smul (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : Pts p H₁),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (g : H₁ →ₐc[ℤ_[p]] H₁) (hg : ∀ a : k, (θ a).comp g = g.comp (θ a)) (a : k) (v : ρbar.V) :
    ptsEnd p H₁ ρbar e₁ g (a • v) = a • ptsEnd p H₁ ρbar e₁ g v := by
  have hθ' : ∀ (a : k) (f : Pts p H₁), e₁ (precomp p H₁ (θ a) f) = a • e₁ f := hθ
  obtain ⟨f, rfl⟩ := e₁.surjective v
  rw [← hθ', ptsEnd_apply_e₁, ptsEnd_apply_e₁, ← precomp_comp, hg, precomp_comp, hθ']

local notation "ιp" => primeLocalToGlobal (pPrime p)

theorem ptsEnd_gal
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : Pts p H₁),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) → e₁ g = ρbar.ρ (ιp σ) (e₁ f))
    (g : H₁ →ₐc[ℤ_[p]] H₁) (σ : primeLocalGaloisGroup (pPrime p)) (v : ρbar.V) :
    ptsEnd p H₁ ρbar e₁ g (ρbar.ρ (ιp σ) v) = ρbar.ρ (ιp σ) (ptsEnd p H₁ ρbar e₁ g v) := by
  obtain ⟨f, rfl⟩ := e₁.surjective v
  rw [← he₁_act σ f (galComp p H₁ σ f) (fun _ => rfl), ptsEnd_apply_e₁, ptsEnd_apply_e₁,
    precomp_galComp, he₁_act σ (precomp p H₁ g f) (galComp p H₁ σ (precomp p H₁ g f)) (fun _ => rfl)]

noncomputable def ptsEndLin (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : Pts p H₁),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (g : H₁ →ₐc[ℤ_[p]] H₁) (hg : ∀ a : k, (θ a).comp g = g.comp (θ a)) : Module.End k ρbar.V where
  toFun := ptsEnd p H₁ ρbar e₁ g
  map_add' := ptsEnd_add p H₁ ρbar e₁ he₁_add g
  map_smul' := ptsEnd_smul p H₁ ρbar e₁ θ hθ g hg

theorem ptsEndLin_apply (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : Pts p H₁),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (g : H₁ →ₐc[ℤ_[p]] H₁) (hg : ∀ a : k, (θ a).comp g = g.comp (θ a)) (v : ρbar.V) :
    ptsEndLin p H₁ ρbar e₁ he₁_add θ hθ g hg v = ptsEnd p H₁ ρbar e₁ g v := rfl

theorem ptsEndLin_mem_invariants (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : Pts p H₁),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) → e₁ g = ρbar.ρ (ιp σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : Pts p H₁),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (g : H₁ →ₐc[ℤ_[p]] H₁) (hg : ∀ a : k, (θ a).comp g = g.comp (θ a)) :
    ptsEndLin p H₁ ρbar e₁ he₁_add θ hθ g hg ∈ (Rep.res ιp (Rep.of ρbar.adRep)).ρ.invariants := by
  rw [Representation.mem_invariants]
  intro σ
  change ρbar.adRep (ιp σ) (ptsEndLin p H₁ ρbar e₁ he₁_add θ hθ g hg) =
    ptsEndLin p H₁ ρbar e₁ he₁_add θ hθ g hg
  rw [ResidualGaloisRep.adRep_apply]
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, ptsEndLin_apply, ptsEndLin_apply,
    ← ptsEnd_gal p H₁ ρbar e₁ he₁_act, ← Module.End.mul_apply (f := ρbar.ρ (ιp σ)), ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end Points

section Transport

variable {k : Type} [Field k] {D : Type} [AddCommGroup D] [Module k D]
variable {M : Type*} [AddCommGroup M] (ι : D ≃+ M)

noncomputable def transport (a : Module.End k D) : M →+ M :=
  ι.toAddMonoidHom.comp (a.toAddMonoidHom.comp ι.symm.toAddMonoidHom)

theorem transport_apply (a : Module.End k D) (z : M) : transport ι a z = ι (a (ι.symm z)) := rfl

theorem transport_injective : Function.Injective (transport (k := k) ι) := by
  intro a b h
  refine LinearMap.ext fun x => ι.injective ?_
  have := DFunLike.congr_fun h (ι x)
  simpa only [transport_apply, AddEquiv.symm_apply_apply] using this

theorem transport_comm (a : Module.End k D) (S : D →ₗ[k] D) (T : M → M)
    (hι : ∀ x, ι (S x) = T (ι x)) (ha : S ∘ₗ a = a ∘ₗ S) (z : M) :
    transport ι a (T z) = T (transport ι a z) := by
  obtain ⟨x, rfl⟩ := ι.surjective z
  rw [transport_apply, transport_apply, AddEquiv.symm_apply_apply, ← hι x,
    AddEquiv.symm_apply_apply, ← hι (a x)]
  congr 1
  exact (LinearMap.congr_fun ha x).symm

theorem transport_mem (a : Module.End k D) (L : Submodule k D) (L' : Set M)
    (hι : ∀ x, x ∈ L ↔ ι x ∈ L') (ha : ∀ x ∈ L, a x ∈ L) (z : M) (hz : z ∈ L') :
    transport ι a z ∈ L' := by
  obtain ⟨x, rfl⟩ := ι.surjective z
  rw [transport_apply, AddEquiv.symm_apply_apply, ← hι]
  exact ha x ((hι x).2 hz)

theorem transport_smul_comm (a : Module.End k D) (c : k) (T : M → M)
    (hι : ∀ x, ι (c • x) = T (ι x)) (z : M) : transport ι a (T z) = T (transport ι a z) := by
  obtain ⟨x, rfl⟩ := ι.surjective z
  rw [transport_apply, transport_apply, AddEquiv.symm_apply_apply, ← hι x,
    AddEquiv.symm_apply_apply, ← hι (a x), map_smul]

end Transport

section Fibre

variable (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (ZMod p)]
variable (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁]

theorem tensorMap_comp (g h : H₁ →ₐc[ℤ_[p]] H₁) :
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (g.comp h) =
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g).comp
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) h) := by
  apply BialgHom.coe_algHom_injective
  rw [BialgHom.comp_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom,
    Bialgebra.TensorProduct.map_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom,
    BialgHom.comp_toAlgHom]
  exact Algebra.TensorProduct.map_id_comp _ _

theorem dieudonneMap_comp_apply (g h : H₁ →ₐc[ℤ_[p]] H₁)
    (z : Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁)) :
    Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (g.comp h)) z =
      Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g)
        (Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) h) z) := by
  rw [tensorMap_comp, Deformation.DieudonneModule.map_comp]

end Fibre

end P2mEndHondaBound

open P2mEndHondaBound in
theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2)
    (hunip₁ : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H₁)))
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H₁)
    (hθ_add : ∀ a b : k, WithConv.toConv (θ (a + b) : H₁ →ₐ[ℤ_[p]] H₁) =
      WithConv.toConv (θ a : H₁ →ₐ[ℤ_[p]] H₁) * WithConv.toConv (θ b : H₁ →ₐ[ℤ_[p]] H₁))
    (hθ_zero : WithConv.toConv (θ 0 : H₁ →ₐ[ℤ_[p]] H₁) = 1)
    (D : Type) [AddCommGroup D] [Module k D] [FiniteDimensional k D] (𝓗 : Deformation.HondaSystem (0 : k) D)
    (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
    (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) (ι x))
    (hD : Module.finrank k D = 2) :
    Module.finrank k 𝓗.endHonda ≤
      Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants := by
  classical

  haveI : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  have hp0 : (p : ℤ_[p]) ∈ nonZeroDivisors ℤ_[p] :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card k = p ^ n := by
    haveI := Fintype.ofFinite k
    obtain ⟨n, -, hn⟩ := FiniteField.card k p
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hrank' : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a := ⟨n * 2, by rw [hrank₁, hn, pow_mul]⟩

  obtain ⟨hfaith, hfull⟩ :=
    Deformation.DieudonneModule.map_baseChange_injective_and_exists_map_baseChange_eq
      p hp0 hker H₁ hunip₁ H₁ hrank' hunip₁

  have hex : ∀ a : 𝓗.endHonda, ∃ g : H₁ →ₐc[ℤ_[p]] H₁,
      Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g) =
        transport ι (a : Module.End k D) := by
    intro a
    obtain ⟨hL, hF, hV⟩ := (𝓗.mem_endHonda_iff (a : Module.End k D)).1 a.2
    exact hfull (transport ι (a : Module.End k D))
      (transport_comm ι (a : Module.End k D) 𝓗.F _ hιF hF)
      (transport_comm ι (a : Module.End k D) 𝓗.V _ hιV hV)
      (transport_mem ι (a : Module.End k D) 𝓗.L _ hιL hL)
  choose g hg using hex

  have hgθ : ∀ (a : 𝓗.endHonda) (c : k), (θ c).comp (g a) = (g a).comp (θ c) := by
    intro a c
    refine hfaith _ _ (AddMonoidHom.ext fun z => ?_)
    rw [dieudonneMap_comp_apply, dieudonneMap_comp_apply, hg]
    exact (transport_smul_comm ι (a : Module.End k D) c _ (hιsmul c) z).symm

  let Ψ : 𝓗.endHonda → (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants :=
    fun a => ⟨ptsEndLin p H₁ ρbar e₁ he₁_add θ hθ (g a) (hgθ a),
      ptsEndLin_mem_invariants p H₁ ρbar e₁ he₁_add he₁_act θ hθ (g a) (hgθ a)⟩

  refine finrank_le_of_injective Ψ fun a b hab => ?_
  have hE : ∀ v, ptsEnd p H₁ ρbar e₁ (g a) v = ptsEnd p H₁ ρbar e₁ (g b) v := fun v => by
    have := congrArg (fun x : (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants
      => (x : Module.End k ρbar.V) v) hab
    simpa only [Ψ, ptsEndLin_apply] using this

  letI := galAction p ρbar
  have he₁_act' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f f' : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, f' x = σ (f x)) →
        e₁ f' = σ • e₁ f :=
    fun σ f f' h => he₁_act (toLoc p σ) f f' h
  let φ : ρbar.V →+ ρbar.V := (ptsEndLin p H₁ ρbar e₁ he₁_add θ hθ (g a) (hgθ a)).toAddMonoidHom
  have hφ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ρbar.V), φ (σ • m) = σ • φ m :=
    fun σ m => ptsEnd_gal p H₁ ρbar e₁ he₁_act (g a) (toLoc p σ) m
  have hu := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
    p hp2 H₁ hrank' e₁ he₁_add he₁_act' H₁ hrank' e₁ he₁_add he₁_act' φ hφ
  have hgab : g a = g b :=
    hu.unique (fun f => (ptsEnd_apply_e₁ p H₁ ρbar e₁ (g a) f).symm)
      (fun f => ((hE (e₁ f)).trans (ptsEnd_apply_e₁ p H₁ ρbar e₁ (g b) f)).symm)
  have hta : transport ι (a : Module.End k D) = transport ι (b : Module.End k D) := by
    rw [← hg a, ← hg b, hgab]
  exact Subtype.ext (transport_injective ι hta)

end S_ResidualGaloisRep_finrank_endHonda_le_finrank_invariants_of_hondaSystem_model
end P2MW
export P2MW.S_ResidualGaloisRep_finrank_endHonda_le_finrank_invariants_of_hondaSystem_model (solution)
