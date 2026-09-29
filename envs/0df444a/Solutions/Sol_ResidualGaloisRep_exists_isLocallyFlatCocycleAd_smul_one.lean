-- Prove2me | solution 1 for ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e801f07d-0612-5ffb-849b-1e641beec146

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero
import Theorems.Thm_ResidualGaloisRep_exists_finiteFlat_padicInt_model_of_isLocallyFlatCocycleAd
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
import Theorems.Thm_PadicInt_exists_etale_algebra_algHom_equiv_zmod
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_model_pi_algHom_of_etale
import Theorems.Thm_ResidualGaloisRep_exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_isLocallyFlatCocycleAd_smul_one
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule instIsScalarTowerTensorProduct_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped TensorProduct PadicInt

namespace E90SF

def IndFun (ℓ : ℕ) (V : Type) : Type := ZMod ℓ → V

scoped instance (ℓ : ℕ) (V : Type) [AddCommGroup V] : AddCommGroup (IndFun ℓ V) :=
  inferInstanceAs (AddCommGroup (ZMod ℓ → V))

@[reducible] def indAction {Γ : Type} [Group Γ] {ℓ : ℕ} (χ : Γ →* Multiplicative (ZMod ℓ))
    {V : Type} [AddCommGroup V] [DistribMulAction Γ V] : DistribMulAction Γ (IndFun ℓ V) where
  smul σ F := fun i => σ • (F (i - Multiplicative.toAdd (χ σ)) : V)
  one_smul F := by
    funext i
    show (1 : Γ) • F (i - Multiplicative.toAdd (χ 1)) = F i
    rw [map_one, toAdd_one, sub_zero, one_smul]
  mul_smul σ τ F := by
    funext i
    show (σ * τ) • F (i - Multiplicative.toAdd (χ (σ * τ))) =
      σ • τ • F (i - Multiplicative.toAdd (χ σ) - Multiplicative.toAdd (χ τ))
    rw [map_mul, toAdd_mul, mul_smul, sub_sub, add_comm]
  smul_zero σ := by
    funext i
    show σ • (0 : V) = 0
    exact smul_zero σ
  smul_add σ F F' := by
    funext i
    show σ • (F _ + F' _) = σ • F _ + σ • F' _
    exact smul_add σ _ _

theorem indAction_smul {Γ : Type} [Group Γ] {ℓ : ℕ} (χ : Γ →* Multiplicative (ZMod ℓ))
    {V : Type} [AddCommGroup V] [DistribMulAction Γ V] (σ : Γ) (F : IndFun ℓ V) (i : ZMod ℓ) :
    (letI := indAction χ (V := V); (σ • F) i) = σ • F (i - Multiplicative.toAdd (χ σ)) := rfl

def DLMod (V : Type) : Type := V × V

scoped instance (V : Type) [AddCommGroup V] : AddCommGroup (DLMod V) := inferInstanceAs (AddCommGroup (V × V))

@[reducible] def dlAction {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
    (act : Γ → V × V → V × V) (h1 : ∀ x, act 1 x = x) (hmul : ∀ σ τ x, act (σ * τ) x = act σ (act τ x))
    (h0 : ∀ σ, act σ 0 = 0) (hadd : ∀ σ x y, act σ (x + y) = act σ x + act σ y) :
    DistribMulAction Γ (DLMod V) where
  smul σ x := act σ x
  one_smul := h1
  mul_smul := hmul
  smul_zero := h0
  smul_add := hadd

def toLoc (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    primeLocalGaloisGroup (pPrime p) := σ

theorem toLoc_one (p : ℕ) [Fact p.Prime] : toLoc p 1 = 1 := rfl

theorem toLoc_mul (p : ℕ) [Fact p.Prime] (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    toLoc p (σ * τ) = toLoc p σ * toLoc p τ := rfl

end E90SF
p2m_reactivate "P2MW.S_ResidualGaloisRep_exists_isLocallyFlatCocycleAd_smul_one.E90SF"

open E90SF in
theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) :
    ∃ (a : primeLocalGaloisGroup (pPrime p) → k)
      (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))),
      (∀ σ, (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ =
          a σ • (1 : Module.End k ρbar.V)) ∧
        (∃ σ, a σ ≠ 0) ∧ ρbar.IsLocallyFlatCocycleAd p c := by
  classical

  haveI : Finite k := ResidualGaloisRep.finite_of_isLocallyFlatCocycleAd_zero p ρbar hflat
  obtain ⟨ℓ, hℓ⟩ := CharP.exists k
  haveI := hℓ
  haveI hℓp : Fact ℓ.Prime :=
    ⟨(CharP.char_is_prime_or_zero k ℓ).resolve_right (CharP.char_ne_zero_of_finite k ℓ)⟩

  obtain ⟨B, _, _, hBfin, hBfree, hBet, χ, x, hχ, hx⟩ :=
    PadicInt.exists_etale_algebra_algHom_equiv_zmod p ℓ hℓp.out.pos
  haveI := hBfin; haveI := hBfree; haveI := hBet

  let πg : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    localGaloisToGlobal p
  letI actV : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ρbar.V :=
    DistribMulAction.compHom ρbar.V ((ρbar.ρ : _ →* Module.End k ρbar.V).comp πg)
  have smulV : ∀ (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (v : ρbar.V), τ • v = ρbar.ρ (πg τ) v :=
    fun _ _ => rfl

  obtain ⟨H₁, _, _, fin₁, fl₁, cc₁, e₁, he₁_add, he₁_act⟩ :=
    ResidualGaloisRep.exists_finiteFlat_padicInt_model_of_isLocallyFlatCocycleAd p ρbar 0 hflat
  haveI := fin₁; haveI := fl₁; haveI := cc₁
  have he₁_act' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ y : H₁, g y = σ (f y)) → e₁ g = σ • (e₁ f) := by
    intro σ f g hfg
    rw [smulV]
    exact he₁_act (ResidualGaloisRep.localAut p σ) f g hfg

  obtain ⟨H₂, _, _, fin₂, fl₂, cc₂, e₂, he₂_add, he₂_act⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_model_pi_algHom_of_etale p H₁ e₁ he₁_add he₁_act' B
  haveI := fin₂; haveI := fl₂; haveI := cc₂

  letI actI : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (IndFun ℓ ρbar.V) := indAction χ
  let e₂' : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ IndFun ℓ ρbar.V :=
    e₂.trans (Equiv.arrowCongr x.symm (Equiv.refl _))
  have e₂'_apply : ∀ f i, e₂' f i = e₂ f (x i) := fun f i => rfl
  have he₂'_add : ∀ f g, e₂' (f * g) = e₂' f + e₂' g := by
    intro f g
    funext i
    show e₂' (f * g) i = e₂' f i + e₂' g i
    rw [e₂'_apply, e₂'_apply, e₂'_apply, he₂_add]
    rfl
  have he₂'_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ y : H₂, g y = σ (f y)) → e₂' g = σ • (e₂' f) := by
    intro σ f g hfg
    funext i
    rw [indAction_smul, e₂'_apply, e₂'_apply]
    have hi : x i = ((σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).restrictScalars ℤ_[p]).comp
        (x (i - Multiplicative.toAdd (χ σ))) := by
      rw [← hx σ (i - Multiplicative.toAdd (χ σ)), add_sub_cancel]
    rw [hi]
    exact he₂_act σ f g hfg _

  let locHom : primeLocalGaloisGroup (pPrime p) →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    { toFun := ResidualGaloisRep.localAut p, map_one' := rfl, map_mul' := fun _ _ => rfl }
  obtain ⟨a, c, hca, ha_ne, ha_mul, π, hπ_surj, hπ_eq⟩ :=
    ResidualGaloisRep.exists_cocycle_smul_one_surjective_pi_dualLiftModuleActAd p ρbar ℓ (χ.comp locHom)
      (fun m => by obtain ⟨σ, hσ⟩ := hχ m; exact ⟨σ, hσ⟩)
  have ha1 : a 1 = 0 := by simpa using ha_mul 1 1

  have hdl : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (y : ρbar.V × ρbar.V),
      ρbar.dualLiftModuleActAd p c σ y =
        (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) y.1,
          a σ • ρbar.ρ (primeLocalToGlobal (pPrime p) σ) y.1 +
            ρbar.ρ (primeLocalToGlobal (pPrime p) σ) y.2) := by
    intro σ y
    simp only [ResidualGaloisRep.dualLiftModuleActAd, hca, LinearMap.smul_apply, Module.End.one_apply]
  let act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ρbar.V × ρbar.V → ρbar.V × ρbar.V :=
    fun σ y => ρbar.dualLiftModuleActAd p c (toLoc p σ) y
  have act_def : ∀ σ y, act σ y = ρbar.dualLiftModuleActAd p c (toLoc p σ) y := fun _ _ => rfl
  have hR1 : ρbar.ρ (primeLocalToGlobal (pPrime p) (toLoc p 1)) = 1 := by
    rw [toLoc_one, map_one, map_one]
  have hRmul : ∀ σ τ, ρbar.ρ (primeLocalToGlobal (pPrime p) (toLoc p (σ * τ))) =
      ρbar.ρ (primeLocalToGlobal (pPrime p) (toLoc p σ)) * ρbar.ρ (primeLocalToGlobal (pPrime p) (toLoc p τ)) := by
    intro σ τ
    rw [toLoc_mul, map_mul, map_mul]
  have h1 : ∀ y, act 1 y = y := by
    intro y
    rw [act_def, hdl, hR1, toLoc_one, ha1]
    simp
  have hmul : ∀ σ τ y, act (σ * τ) y = act σ (act τ y) := by
    intro σ τ y
    rw [act_def, act_def, act_def, hdl, hdl, hdl, hRmul, toLoc_mul, ha_mul]
    ext
    · simp [Module.End.mul_apply]
    · simp only [Module.End.mul_apply, map_add, map_smul, add_smul, smul_add]
      abel
  have h0 : ∀ σ, act σ 0 = 0 := by
    intro σ
    rw [act_def, hdl]
    simp
  have hadd : ∀ σ y z, act σ (y + z) = act σ y + act σ z := by
    intro σ y z
    rw [act_def, act_def, act_def, hdl, hdl, hdl]
    ext
    · simp [map_add]
    · simp only [Prod.snd_add, Prod.fst_add, map_add, smul_add]
      abel
  letI actD : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (DLMod ρbar.V) :=
    dlAction act h1 hmul h0 hadd
  have smulD : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : DLMod ρbar.V),
      σ • y = ρbar.dualLiftModuleActAd p c (toLoc p σ) (y : ρbar.V × ρbar.V) := fun _ _ => rfl

  let π' : IndFun ℓ ρbar.V →+ DLMod ρbar.V := π
  have hπ'_surj : Function.Surjective π' := hπ_surj
  have hπ'_eq : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F : IndFun ℓ ρbar.V),
      π' (σ • F) = σ • π' F := by
    intro σ F
    rw [smulD]
    exact hπ_eq (toLoc p σ) F

  obtain ⟨H₃, _, _, fin₃, fl₃, cc₃, e₃, he₃_add, he₃_act⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_quotient_of_equivariant_surjection p H₂ e₂' he₂'_add he₂'_act
      π' hπ'_surj hπ'_eq
  refine ⟨a, c, hca, ha_ne, H₃, inferInstance, inferInstance, fin₃, fl₃, cc₃, e₃, he₃_add, ?_⟩
  intro σ f g hfg
  exact he₃_act (ResidualGaloisRep.localAut p σ) f g hfg

end S_ResidualGaloisRep_exists_isLocallyFlatCocycleAd_smul_one
end P2MW
export P2MW.S_ResidualGaloisRep_exists_isLocallyFlatCocycleAd_smul_one (solution)
