-- Prove2me | solution 1 for ResidualGaloisRep.exists_unipotent_model_V_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cbb5336b-0f45-5c89-9347-e6ff14289361

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
import Theorems.Thm_HopfAlgebra_free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_unipotent_model_V_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply"
p2m_attr_erase "simp" "CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt TensorProduct

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
    ∃ (H₁ : Type) (_ : CommRing H₁) (_ : HopfAlgebra ℤ_[p] H₁) (_ : Module.Finite ℤ_[p] H₁)
      (_ : Module.Free ℤ_[p] H₁) (_ : Coalgebra.IsCocomm ℤ_[p] H₁),
      Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2 ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H₁)) ∧
      ∃ e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V,
        (∀ f g, e₁ (f * g) = e₁ f + e₁ g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f) := by
  classical
  obtain ⟨H, _, _, hfin, hflat, hcoc, hunipH, e, he_add, he_act⟩ := hunip
  haveI := hfin; haveI := hflat; haveI := hcoc

  let θ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Module.End k ρbar.V :=
    ρbar.ρ.comp (primeLocalToGlobal (pPrime p))
  letI instV : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ρbar.V :=
    DistribMulAction.compHom ρbar.V θ
  have smul_def : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (v : ρbar.V),
      σ • v = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v := fun _ _ => rfl

  have act0 : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ρbar.V × ρbar.V),
      ρbar.dualLiftModuleActAd p 0 σ x = σ • x := by
    intro σ x
    refine Prod.ext rfl ?_
    show _ + ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2 = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2
    convert (zero_add (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2)) using 2 <;> rfl
  have he_act' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by
    intro σ f g hfg
    rw [← act0]
    exact he_act σ f g hfg

  obtain ⟨H₁, _, _, hfin₁, hflat₁, hcoc₁, e₁, he₁_add, he₁_act⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_quotient_of_equivariant_surjection p H e he_add he_act'
      (AddMonoidHom.fst ρbar.V ρbar.V) Prod.fst_surjective (fun σ m => rfl)
  haveI := hfin₁; haveI := hflat₁; haveI := hcoc₁

  haveI := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k p
  have hk : Nat.card k = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hV : Nat.card ρbar.V = p ^ (2 * (n : ℕ)) := by
    rw [Module.natCard_eq_pow_finrank (K := k), hk, ρbar.finrank_eq, ← pow_mul, mul_comm]
  have hVV : Nat.card (ρbar.V × ρbar.V) = p ^ (2 * (n : ℕ) + 2 * (n : ℕ)) := by
    rw [Nat.card_prod, hV, pow_add]
  haveI : Finite ρbar.V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨hfreeH, hrankH⟩ :=
    HopfAlgebra.free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq p H e _ hVV
  obtain ⟨hfree₁, hrank₁⟩ :=
    HopfAlgebra.free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq p H₁ e₁ _ hV
  haveI := hfreeH; haveI := hfree₁

  have hι_eq : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (v : ρbar.V),
      AddMonoidHom.inl ρbar.V ρbar.V (σ • v) = σ • AddMonoidHom.inl ρbar.V ρbar.V v := by
    intro σ v
    exact Prod.ext rfl (smul_zero σ).symm
  obtain ⟨s, hs, -⟩ :=
    HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two p hp2
      H₁ ⟨_, hrank₁⟩ e₁ he₁_add he₁_act H ⟨_, hrankH⟩ e he_add he_act'
      (AddMonoidHom.inl ρbar.V ρbar.V) hι_eq
  obtain ⟨u, hu, -⟩ :=
    HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two p hp2
      H ⟨_, hrankH⟩ e he_add he_act' H₁ ⟨_, hrank₁⟩ e₁ he₁_add he₁_act
      (AddMonoidHom.fst ρbar.V ρbar.V) (fun σ m => rfl)
  have hEU :=
    HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two p hp2
      H₁ ⟨_, hrank₁⟩ e₁ he₁_add he₁_act H₁ ⟨_, hrank₁⟩ e₁ he₁_add he₁_act
      (AddMonoidHom.id ρbar.V) (fun σ m => rfl)
  have h_su : ∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (s.comp u : H₁ →ₐ[ℤ_[p]] H₁))) = AddMonoidHom.id _ (e₁ f) := by
    intro f
    have h1 : (WithConv.ofConv f).comp (s.comp u : H₁ →ₐ[ℤ_[p]] H₁) =
        (WithConv.ofConv (WithConv.toConv ((WithConv.ofConv f).comp (s : H →ₐ[ℤ_[p]] H₁)))).comp
          (u : H₁ →ₐ[ℤ_[p]] H) := by
      rw [WithConv.ofConv_toConv]; rfl
    rw [h1, hu, hs]
    rfl
  have h_id : ∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (BialgHom.id ℤ_[p] H₁ : H₁ →ₐ[ℤ_[p]] H₁))) = AddMonoidHom.id _ (e₁ f) := by
    intro f
    have : (WithConv.ofConv f).comp (BialgHom.id ℤ_[p] H₁ : H₁ →ₐ[ℤ_[p]] H₁) = WithConv.ofConv f := by
      ext x; rfl
    rw [this, WithConv.toConv_ofConv]
    rfl
  have hsu_eq : s.comp u = BialgHom.id ℤ_[p] H₁ := hEU.unique h_su h_id
  have hs_surj : Function.Surjective s := by
    intro y
    refine ⟨u y, ?_⟩
    have := congrArg (fun φ : H₁ →ₐc[ℤ_[p]] H₁ => φ y) hsu_eq
    simpa using this

  let sbar : TensorProduct ℤ_[p] (ZMod p) H →ₐc[ZMod p] TensorProduct ℤ_[p] (ZMod p) H₁ :=
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) s
  have hsbar : Function.Surjective sbar := by
    have : (sbar : TensorProduct ℤ_[p] (ZMod p) H → TensorProduct ℤ_[p] (ZMod p) H₁) =
        TensorProduct.map (LinearMap.id : ZMod p →ₗ[ℤ_[p]] ZMod p) (s : H →ₐ[ℤ_[p]] H₁).toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp [sbar]
      | tmul a b => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [this]
    exact TensorProduct.map_surjective Function.surjective_id hs_surj
  have hunip₁ : IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H₁)) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)
      (TensorProduct ℤ_[p] (ZMod p) H₁) sbar hsbar hunipH

  refine ⟨H₁, inferInstance, inferInstance, hfin₁, hfree₁, hcoc₁, ?_, hunip₁, e₁, he₁_add, ?_⟩
  · rw [hrank₁, hk, ← pow_mul, mul_comm]
  · intro σ f g hfg
    exact he₁_act σ f g hfg

end S_ResidualGaloisRep_exists_unipotent_model_V_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_ResidualGaloisRep_exists_unipotent_model_V_of_isLocalRing_cartierDual (solution)
