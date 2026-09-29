-- Prove2me | solution 1 for ResidualGaloisRep.isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6680e66a-b199-5573-adf3-4d9d6e0eee7f

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_quotient_of_equivariant_surjection
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_model_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

open scoped PadicInt

namespace E88NF

variable (p : ℕ) [Fact p.Prime]

local notation "L" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section transport

variable {p}
variable {H : Type} [CommRing H] [HopfAlgebra ℤ_[p] H]

noncomputable def gal (τ : Γ) (f : WithConv (H →ₐ[ℤ_[p]] L)) : WithConv (H →ₐ[ℤ_[p]] L) :=
  WithConv.toConv ((τ.toAlgHom.restrictScalars ℤ_[p]).comp (WithConv.ofConv f))

theorem gal_apply (τ : Γ) (f : WithConv (H →ₐ[ℤ_[p]] L)) (h : H) : gal τ f h = τ (f h) := rfl

theorem gal_one (f : WithConv (H →ₐ[ℤ_[p]] L)) : gal 1 f = f := by
  apply congrArg WithConv.toConv (AlgHom.ext fun h => rfl) |>.trans
  exact WithConv.toConv_ofConv f

theorem gal_mul (σ τ : Γ) (f : WithConv (H →ₐ[ℤ_[p]] L)) : gal (σ * τ) f = gal σ (gal τ f) := by
  apply congrArg WithConv.toConv
  apply AlgHom.ext
  intro h
  rfl

theorem convMul_apply_repr (f g : WithConv (H →ₐ[ℤ_[p]] L)) {h : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr ℤ_[p] h ι𝓡) :
    (f * g) h = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  have := congrArg (fun (φ : WithConv (H →ₗ[ℤ_[p]] L)) => (WithConv.ofConv φ) h)
    (AlgHom.toLinearMap_convMul f g)
  simp only [AlgHom.toLinearMap_apply] at this
  rw [this, Coalgebra.Repr.convMul_apply 𝓡]
  rfl

theorem gal_convMul (τ : Γ) (f g : WithConv (H →ₐ[ℤ_[p]] L)) : gal τ (f * g) = gal τ f * gal τ g := by
  classical
  have hext : ∀ (F G : WithConv (H →ₐ[ℤ_[p]] L)), (∀ h : H, F h = G h) → F = G := by
    intro F G hFG
    have : WithConv.ofConv F = WithConv.ofConv G := AlgHom.ext hFG
    simpa using congrArg WithConv.toConv this
  apply hext
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary ℤ_[p] h
  rw [gal_apply, convMul_apply_repr f g 𝓡, convMul_apply_repr _ _ 𝓡, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]; rfl

theorem gal_convOne (τ : Γ) : gal τ (1 : WithConv (H →ₐ[ℤ_[p]] L)) = 1 := by
  have hext : ∀ (F G : WithConv (H →ₐ[ℤ_[p]] L)), (∀ h : H, F h = G h) → F = G := by
    intro F G hFG
    have : WithConv.ofConv F = WithConv.ofConv G := AlgHom.ext hFG
    simpa using congrArg WithConv.toConv this
  apply hext
  intro h
  rw [gal_apply, AlgHom.convOne_apply]
  exact (τ.toAlgHom.restrictScalars ℤ_[p]).commutes _

def EcMod (V : Type) : Type := V × V

scoped instance (V : Type) [AddCommGroup V] : AddCommGroup (EcMod V) := inferInstanceAs (AddCommGroup (V × V))

@[reducible] noncomputable def transported {V : Type} [AddCommGroup V] (e : WithConv (H →ₐ[ℤ_[p]] L) ≃ EcMod V)
    (he_add : ∀ f g, e (f * g) = e f + e g) :
    DistribMulAction Γ (EcMod V) :=
  have he_one : e 1 = 0 := by
    have h := he_add 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  { smul := fun τ m => e (gal τ (e.symm m))
    one_smul := fun m => by
      show e (gal 1 (e.symm m)) = m
      rw [gal_one, Equiv.apply_symm_apply]
    mul_smul := fun σ τ m => by
      show e (gal (σ * τ) (e.symm m)) = e (gal σ (e.symm (e (gal τ (e.symm m)))))
      rw [gal_mul, Equiv.symm_apply_apply]
    smul_zero := fun τ => by
      show e (gal τ (e.symm 0)) = 0
      have : e.symm 0 = 1 := by rw [Equiv.symm_apply_eq]; exact he_one.symm
      rw [this, gal_convOne]; exact he_one
    smul_add := fun τ a b => by
      show e (gal τ (e.symm (a + b))) = e (gal τ (e.symm a)) + e (gal τ (e.symm b))
      have : e.symm (a + b) = e.symm a * e.symm b := by
        rw [Equiv.symm_apply_eq, he_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [this, gal_convMul]
      exact he_add _ _ }

theorem transported_smul {V : Type} [AddCommGroup V] (e : WithConv (H →ₐ[ℤ_[p]] L) ≃ EcMod V)
    (he_add : ∀ f g, e (f * g) = e f + e g) (τ : Γ) (m : EcMod V) :
    (letI := transported e he_add; τ • m) = e (gal τ (e.symm m)) := rfl

end transport

end E88NF
p2m_reactivate "P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle.E88NF"

open E88NF in

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρbar : ResidualGaloisRep k)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero))
    (hc : ρbar.IsLocallyFlatCocycle p c) :
    ρbar.IsLocallyFlatCocycleAd p 0 := by
  classical
  obtain ⟨H, _, _, hfin, hfl, hcc, e, he_add, he_act⟩ := hc
  haveI := hfin; haveI := hfl; haveI := hcc
  let πg : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    localGaloisToGlobal p

  letI actV : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ρbar.V :=
    DistribMulAction.compHom ρbar.V ((ρbar.ρ : _ →* Module.End k ρbar.V).comp πg)
  have smulV : ∀ (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (v : ρbar.V), τ • v = ρbar.ρ (πg τ) v :=
    fun _ _ => rfl

  let eE : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ EcMod ρbar.V := e
  have heE_add : ∀ f g, eE (f * g) = eE f + eE g := he_add
  letI actE : DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (EcMod ρbar.V) := transported eE heE_add
  have smulE : ∀ (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : EcMod ρbar.V),
      τ • m = eE (gal τ (eE.symm m)) := fun τ m => transported_smul eE heE_add τ m

  have heE_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : H, g x = σ (f x)) → eE g = σ • (eE f) := by
    intro σ f g hfg
    rw [smulE, Equiv.symm_apply_apply]
    congr 1
    have : WithConv.ofConv g = WithConv.ofConv (gal σ f) := AlgHom.ext fun x => hfg x
    simpa using congrArg WithConv.toConv this

  have hactE : ∀ (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : EcMod ρbar.V),
      τ • m = ρbar.dualLiftModuleAct p c τ (m : ρbar.V × ρbar.V) := by
    intro τ m
    rw [smulE]
    have h := he_act τ (eE.symm m) (gal τ (eE.symm m)) (fun h => rfl)
    have hm : e (eE.symm m) = m := eE.apply_symm_apply m
    rw [hm] at h
    exact h

  let π₁ : EcMod ρbar.V →+ ρbar.V := AddMonoidHom.fst ρbar.V ρbar.V
  have hπ₁ : Function.Surjective π₁ := Prod.fst_surjective
  have hπ₁_eq : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : EcMod ρbar.V), π₁ (σ • m) = σ • π₁ m := by
    intro σ m
    rw [hactE, smulV]
    rfl

  obtain ⟨H₁, _, _, hfin₁, hfl₁, hcc₁, e₁, he₁_add, he₁_act⟩ :=
    HopfAlgebra.exists_finiteFlat_padicInt_quotient_of_equivariant_surjection p H eE heE_add heE_act π₁ hπ₁ hπ₁_eq
  haveI := hfin₁; haveI := hfl₁; haveI := hcc₁

  haveI : SMulCommClass (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℤ_[p] (PadicAlgCl p) :=
    ⟨fun σ r x => by
      show σ (r • x) = r • σ x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact (σ.toAlgHom.restrictScalars ℤ_[p]).commutes r⟩
  have he₁_act' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : H₁, g x = σ • (f x)) → e₁ g = σ • (e₁ f) := fun σ f g hfg => he₁_act σ f g hfg
  obtain ⟨H₂, _, _, hfin₂, hfl₂, hcc₂, e₂, he₂_add, he₂_act⟩ :=
    HopfAlgebra.exists_finiteFlat_model_prod H₁ e₁ he₁_add he₁_act' H₁ e₁ he₁_add he₁_act'
  refine ⟨H₂, inferInstance, inferInstance, hfin₂, hfl₂, hcc₂, e₂, he₂_add, ?_⟩
  intro σ f g hfg
  have h := he₂_act (ResidualGaloisRep.localAut p σ) f g (fun x => hfg x)
  rw [h]

  show ((ResidualGaloisRep.localAut p σ) • (e₂ f).1, (ResidualGaloisRep.localAut p σ) • (e₂ f).2) = _
  rw [smulV, smulV, ResidualGaloisRep.dualLiftModuleActAd]
  have h0 : ∀ x : ρbar.V, ((0 : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :
      primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ x = 0 := fun x => rfl
  rw [h0, zero_add]
  rfl

end S_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle
end P2MW
export P2MW.S_ResidualGaloisRep_isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle (solution)
