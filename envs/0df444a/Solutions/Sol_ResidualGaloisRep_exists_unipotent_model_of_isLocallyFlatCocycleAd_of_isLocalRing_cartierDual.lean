-- Prove2me | solution 1 for ResidualGaloisRep.exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ed5584ae-132a-59b9-a091-eb806f4a04bd

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_connected_etale_sequence_padicInt
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one
import Theorems.Thm_CartierDual_exists_equiv_algHom_padicAlgCl_monoidHom_units
import Theorems.Thm_CartierDual_nonempty_ringEquiv_baseChange
import Theorems.Thm_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
import Theorems.Thm_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt TensorProduct Pointwise

namespace S17
namespace ExtUnip

variable (p : ℕ) [Fact p.Prime]

theorem mem_decompositionSubgroup (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    τ ∈ (padicIntegers p).decompositionSubgroup ℚ_[p] := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    mem_padicIntegers_iff, mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

theorem conj_mem_inertiaSubgroupIn {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    τ * σ * τ⁻¹ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
  change σ ∈ Subgroup.map _ _ at hσ
  change τ * σ * τ⁻¹ ∈ Subgroup.map _ _
  rw [Subgroup.mem_map] at hσ ⊢
  obtain ⟨d, hd, rfl⟩ := hσ
  have hN : ((padicIntegers p).inertiaSubgroup ℚ_[p]).Normal := MonoidHom.normal_ker _
  let t : ↥((padicIntegers p).decompositionSubgroup ℚ_[p]) := ⟨τ, mem_decompositionSubgroup p τ⟩
  refine ⟨t * d * t⁻¹, hN.conj_mem d hd t, ?_⟩
  simp [t]

theorem conj_pow_clause {σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {c : ℕ}
    (hc : ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) :
    ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → (τ⁻¹ * σ * τ) ζ = ζ ^ c := by
  intro ζ hζ
  have hτζ : (τ ζ) ^ p = 1 := by rw [← map_pow, hζ, map_one]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc _ hτζ, map_pow, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_apply]

theorem no_omega_vector {k : Type} [Field k] [Finite k] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hunip : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (v : ρbar.V)
    (hv : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ n : ℕ,
          (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ n) →
            ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v = (n : k) • v) :
    v = 0 := by
  classical
  obtain ⟨H, instCR, instHA, hfin, hfl, hco, hloc, e, he_add, he_act⟩ := hunip
  haveI : Module.Flat ℤ_[p] H := hfl
  haveI : Coalgebra.IsCocomm ℤ_[p] H := hco
  haveI : Module.Finite ℤ_[p] H := hfin
  have he1 : e 1 = 0 := by
    have h := he_add 1 1
    rw [mul_one] at h
    have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have he_pow : ∀ (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) (n : ℕ), e (f ^ n) = n • e f := by
    intro f n
    induction n with
    | zero => rw [pow_zero, zero_smul, he1]
    | succ n ih => rw [pow_succ, he_add, ih, succ_nsmul]
  let f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := e.symm (v, 0)
  have hef : e f = (v, 0) := e.apply_symm_apply _
  have hfp : f ^ p = 1 := by
    apply e.injective
    rw [he_pow, hef, he1]
    show p • (v, (0 : ρbar.V)) = 0
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have hfI : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ n : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ n) →
        ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), (∀ h : H, g h = σ (f h)) → g = f ^ n := by
    intro σ hσ n hn g hg
    have key : e g = ρbar.dualLiftModuleActAd p 0 σ (e f) := he_act σ f g hg
    apply e.injective
    rw [key, he_pow, hef]
    refine Prod.ext ?_ ?_
    · show ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v = (n • (v, (0 : ρbar.V))).1
      rw [Prod.smul_fst, hv σ hσ n hn, Nat.cast_smul_eq_nsmul]
    · show ((0 : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :
          primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ
            (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v)
          + ρbar.ρ (primeLocalToGlobal (pPrime p) σ) 0 = (n • (v, (0 : ρbar.V))).2
      have h0 : ((0 : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :
          primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ
            (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v) = 0 := rfl
      rw [h0, zero_add, map_zero, Prod.smul_snd, smul_zero]
  have h1 : f = 1 :=
    HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt
      p hp2 hker H hloc f hfp hfI
  have hv0 : (v, (0 : ρbar.V)) = 0 := by rw [← hef, h1, he1]
  exact congrArg Prod.fst hv0

theorem main
    {k : Type} [Field k] [Finite k] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hunip : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p c σ (e f)  := by
  classical
  let ρ : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V :=
    fun σ => ρbar.ρ (primeLocalToGlobal (pPrime p) σ)
  have noω : ∀ v : ρbar.V, (∀ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ n : ℕ,
        (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ n) →
          ρ σ v = (n : k) • v) → v = 0 :=
    fun v hv => no_omega_vector p hp2 hker ρbar hunip v hv
  obtain ⟨H, instCR, instHA, hfin, hfl, hco, e, he_add, he_act⟩ := hc
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing
  refine ⟨H, instCR, instHA, hfin, hfl, hco, ?_, e, he_add, he_act⟩
  haveI : Module.Flat ℤ_[p] H := hfl
  haveI : Coalgebra.IsCocomm ℤ_[p] H := hco
  haveI : Module.Finite ℤ_[p] H := hfin

  have he1 : e 1 = 0 := by
    have h := he_add 1 1
    rw [mul_one] at h
    have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  let E : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃* Multiplicative (ρbar.V × ρbar.V) :=
    { toEquiv := e.trans Multiplicative.ofAdd
      map_mul' := fun f g => by
        show Multiplicative.ofAdd (e (f * g)) = Multiplicative.ofAdd (e f) * Multiplicative.ofAdd (e g)
        rw [he_add, ofAdd_add] }
  have hE : ∀ f, E f = Multiplicative.ofAdd (e f) := fun _ => rfl
  let pt : ρbar.V × ρbar.V → WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := fun x => E.symm (Multiplicative.ofAdd x)
  have hpt : ∀ x, pt x = e.symm x := fun _ => rfl
  have hept : ∀ x, e (pt x) = x := fun x => by rw [hpt, e.apply_symm_apply]
  have hpt_add : ∀ x y, pt (x + y) = pt x * pt y := by
    intro x y
    show E.symm (Multiplicative.ofAdd (x + y)) = _
    rw [ofAdd_add, map_mul]
  have hpt_nsmul : ∀ (n : ℕ) x, pt (n • x) = pt x ^ n := by
    intro n x
    show E.symm (Multiplicative.ofAdd (n • x)) = _
    rw [ofAdd_nsmul, map_pow]
  let gal : primeLocalGaloisGroup (pPrime p) → WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →
      WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := fun σ f =>
    WithConv.toConv (((ResidualGaloisRep.localAut p σ).toAlgHom.restrictScalars ℤ_[p]).comp
      (WithConv.ofConv f))
  have hgal : ∀ σ f (h : H), gal σ f h = ResidualGaloisRep.localAut p σ (f h) := fun _ _ _ => rfl
  have hpt_gal : ∀ σ x, pt (ρbar.dualLiftModuleActAd p c σ x) = gal σ (pt x) := by
    intro σ x
    apply e.injective
    rw [he_act σ (pt x) (gal σ (pt x)) (hgal σ (pt x)), hept, hept]

  have hgg : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      gal σ (gal σ⁻¹ f) = f := by
    intro σ f
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    show ResidualGaloisRep.localAut p σ (ResidualGaloisRep.localAut p σ⁻¹ (f h)) = f h
    rw [show ResidualGaloisRep.localAut p σ⁻¹ = (ResidualGaloisRep.localAut p σ)⁻¹ from rfl,
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hact_inv : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V),
      ρbar.dualLiftModuleActAd p c σ (ρbar.dualLiftModuleActAd p c σ⁻¹ x) = x := by
    intro σ x
    have h1 : pt (ρbar.dualLiftModuleActAd p c σ (ρbar.dualLiftModuleActAd p c σ⁻¹ x)) = pt x := by
      rw [hpt_gal, hpt_gal, hgg]
    have h2 := congrArg e h1
    rwa [hept, hept] at h2

  obtain ⟨H₀, _, _, Hₑ, _, _, π, ι, hfin0, hfree0, hco0, hloc0, hfinE, hfreeE, hcoE, -, hπsurj, -,
    hιinj, hrange, hrank, hcount, hexact, hext, hinert⟩ :=
    HopfAlgebra.exists_connected_etale_sequence_padicInt p (CartierDual ℤ_[p] H)
  obtain ⟨d, hd_mul, hd_act⟩ := CartierDual.exists_equiv_algHom_padicAlgCl_monoidHom_units p H
  let gal' : primeLocalGaloisGroup (pPrime p) → WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) →
      WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) := fun σ φ =>
    WithConv.toConv (((ResidualGaloisRep.localAut p σ).toAlgHom.restrictScalars ℤ_[p]).comp
      (WithConv.ofConv φ))
  have hgal' : ∀ σ φ (y : CartierDual ℤ_[p] H), gal' σ φ y = ResidualGaloisRep.localAut p σ (φ y) :=
    fun _ _ _ => rfl

  let ιc : Hₑ →ₐ[ℤ_[p]] ↥(HopfAlgebra.hopfKer π) :=
    (ι : Hₑ →ₐ[ℤ_[p]] CartierDual ℤ_[p] H).codRestrict (HopfAlgebra.hopfKer π)
      (fun z => (hrange (ι z)).mpr ⟨z, rfl⟩)
  have hιc_bij : Function.Bijective ιc := by
    refine ⟨fun a b h => hιinj (congrArg Subtype.val h : _), fun y => ?_⟩
    obtain ⟨z, hz⟩ := (hrange y.1).mp y.2
    exact ⟨z, Subtype.ext hz⟩
  haveI : Module.Free ℤ_[p] Hₑ := hfreeE
  haveI : Module.Flat ℤ_[p] ↥(HopfAlgebra.hopfKer π) :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective ιc.toLinearMap hιc_bij).symm
  haveI : Module.Finite ℤ_[p] H₀ := hfin0
  haveI : Module.Free ℤ_[p] H₀ := hfree0
  obtain ⟨hres1, hresmul, -⟩ :=
    HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique π hπsurj (PadicAlgCl p)
  let res : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) →
      WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[ℤ_[p]] PadicAlgCl p) :=
    fun φ => WithConv.toConv ((WithConv.ofConv φ).comp (HopfAlgebra.hopfKer π).val)
  have hres_def : ∀ φ, res φ = WithConv.toConv ((WithConv.ofConv φ).comp (HopfAlgebra.hopfKer π).val) :=
    fun _ => rfl
  have hres_one : res 1 = 1 := hres1
  have hres_mul : ∀ φ ψ, res (φ * ψ) = res φ * res ψ := hresmul
  have hinertK : ∀ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ (h' : ↥(HopfAlgebra.hopfKer π) →ₐ[ℤ_[p]] PadicAlgCl p) (y : ↥(HopfAlgebra.hopfKer π)),
        ResidualGaloisRep.localAut p σ (h' y) = h' y := by
    intro σ hσ h' y
    obtain ⟨z, hz⟩ := (hrange y.1).mp y.2
    have hy : y = ιc z := Subtype.ext hz.symm
    rw [hy]
    exact hinert (ResidualGaloisRep.localAut p σ) hσ (h'.comp ιc) z
  have hres_gal : ∀ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ φ, res (gal' σ φ) = res φ := by
    intro σ hσ φ
    rw [hres_def, hres_def]
    congr 1
    ext y
    exact hinertK σ hσ ((WithConv.ofConv φ).comp (HopfAlgebra.hopfKer π).val) y

  have hinvpt : ∀ φ : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p),
      ∃ ν : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p), φ * ν = 1 ∧ ν * φ = 1 := by
    intro φ
    obtain ⟨ν', -, hl, hr⟩ := HopfAlgebra.exists_comp_antipode_convMul_eq_one (WithConv.ofConv φ)
    exact ⟨WithConv.toConv ν', by simpa using hr, by simpa using hl⟩
  have hd1 : d 1 = 1 := by
    have h := hd_mul 1 1
    rw [mul_one] at h
    exact mul_left_cancel (h.symm.trans (mul_one (d 1)).symm)
  have hdsymm_mul : ∀ χ ψ, d.symm (χ * ψ) = d.symm χ * d.symm ψ := by
    intro χ ψ
    apply d.injective
    rw [hd_mul, d.apply_symm_apply, d.apply_symm_apply, d.apply_symm_apply]
  have hd_inv : ∀ φ ν, φ * ν = 1 → d ν = (d φ)⁻¹ := by
    intro φ ν h
    have h' : d φ * d ν = 1 := by rw [← hd_mul, h, hd1]
    ext f
    have hf := DFunLike.congr_fun h' f
    rw [MonoidHom.mul_apply, MonoidHom.one_apply] at hf
    rw [MonoidHom.inv_apply]
    exact congrArg Units.val (eq_inv_of_mul_eq_one_right hf)

  let 𝒦 : Subgroup (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ) :=
    { carrier := {χ | res (d.symm χ) = 1}
      mul_mem' := fun {χ ψ} hχ hψ => by
        show res (d.symm (χ * ψ)) = 1
        rw [hdsymm_mul, hres_mul, hχ, hψ, mul_one]
      one_mem' := by
        show res (d.symm 1) = 1
        rw [← hd1, d.symm_apply_apply, hres_one]
      inv_mem' := fun {χ} hχ => by
        show res (d.symm χ⁻¹) = 1
        obtain ⟨ν, hν, hν'⟩ := hinvpt (d.symm χ)
        have hdν : d ν = χ⁻¹ := by rw [hd_inv (d.symm χ) ν hν, d.apply_symm_apply]
        rw [← hdν, d.symm_apply_apply]
        have h : res (d.symm χ) * res ν = 1 := by rw [← hres_mul, hν, hres_one]
        rwa [hχ, one_mul] at h }
  have hmem𝒦 : ∀ χ, χ ∈ 𝒦 ↔ res (d.symm χ) = 1 := fun _ => Iff.rfl

  have hcoset : ∀ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ χ, ∃ κ ∈ 𝒦, d (gal' σ (d.symm χ)) = κ * χ := by
    intro σ hσ χ
    obtain ⟨ν, hν, hν'⟩ := hinvpt (d.symm χ)
    refine ⟨d (gal' σ (d.symm χ) * ν), ?_, ?_⟩
    · rw [hmem𝒦, d.symm_apply_apply, hres_mul, hres_gal σ hσ, ← hres_mul, hν, hres_one]
    · rw [hd_mul, hd_inv (d.symm χ) ν hν, d.apply_symm_apply]
      ext f
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_right]

  suffices hloc : IsLocalRing (CartierDual ℤ_[p] H) by
    have hsurjT : Function.Surjective (Algebra.TensorProduct.includeRight :
        CartierDual ℤ_[p] H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] CartierDual ℤ_[p] H) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul a h =>
        obtain ⟨r, rfl⟩ := ZMod.ringHom_surjective (algebraMap ℤ_[p] (ZMod p)) a
        refine ⟨r • h, ?_⟩
        rw [map_smul, Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul',
          TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
    haveI : Nontrivial ((ZMod p) ⊗[ℤ_[p]] CartierDual ℤ_[p] H) :=
      (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (ZMod p))
        (Bialgebra.counitAlgHom ℤ_[p] (CartierDual ℤ_[p] H))).toRingHom.domain_nontrivial
    haveI : IsLocalRing ((ZMod p) ⊗[ℤ_[p]] CartierDual ℤ_[p] H) := IsLocalRing.of_surjective'
      (Algebra.TensorProduct.includeRight :
        CartierDual ℤ_[p] H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] CartierDual ℤ_[p] H).toRingHom hsurjT
    obtain ⟨ψ⟩ := CartierDual.nonempty_ringEquiv_baseChange ℤ_[p] (ZMod p) H
    haveI : Nontrivial (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)) := ψ.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' ψ.symm.toRingHom ψ.symm.surjective
  by_cases htop : 𝒦 = ⊤
  ·
    have hall : ∀ φ : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p), res φ = 1 := by
      intro φ
      have h : d φ ∈ 𝒦 := by rw [htop]; exact Subgroup.mem_top _
      rwa [hmem𝒦, d.symm_apply_apply] at h
    have htrivE : ∀ h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p,
        h = (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] Hₑ) := by
      intro h
      obtain ⟨f, hf⟩ := hext h
      rw [← hf]
      have h1 : res (WithConv.toConv f) = 1 := hall _
      have h2 : f.comp (HopfAlgebra.hopfKer π).val =
          (WithConv.ofConv (1 : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p))).comp
            (HopfAlgebra.hopfKer π).val := by
        have h' := congrArg WithConv.ofConv (h1.trans hres_one.symm)
        simpa [hres_def] using h'
      have h3 : f.comp (ι : Hₑ →ₐ[ℤ_[p]] CartierDual ℤ_[p] H) =
          (f.comp (HopfAlgebra.hopfKer π).val).comp ιc := by
        ext z; rfl
      rw [h3, h2]
      ext z
      change (WithConv.ofConv (1 : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p))) (ι z) =
        algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit z)
      rw [← CoalgHomClass.counit_comp_apply (ι : Hₑ →ₐc[ℤ_[p]] CartierDual ℤ_[p] H) z]
      rfl
    have hcard1 : Nat.card (Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨_, htrivE⟩
    have hrkE : Module.finrank ℤ_[p] Hₑ = 1 := by rw [← hcount, hcard1]
    have hrk : Module.finrank ℤ_[p] (CartierDual ℤ_[p] H) = Module.finrank ℤ_[p] H₀ := by
      rw [hrank, hrkE, mul_one]
    have hπinj : Function.Injective π := by
      have iso := LinearEquiv.ofFinrankEq (CartierDual ℤ_[p] H) H₀ hrk
      exact OrzechProperty.injective_of_surjective_of_injective iso.toLinearMap
        (π : CartierDual ℤ_[p] H →ₐ[ℤ_[p]] H₀).toLinearMap iso.injective hπsurj
    haveI : IsLocalRing H₀ := hloc0
    let eqv : CartierDual ℤ_[p] H ≃+* H₀ :=
      RingEquiv.ofBijective (π : CartierDual ℤ_[p] H →ₐ[ℤ_[p]] H₀) ⟨hπinj, hπsurj⟩
    haveI : Nontrivial (CartierDual ℤ_[p] H) := eqv.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' (eqv.symm : H₀ →+* CartierDual ℤ_[p] H) eqv.symm.surjective
  ·
    exfalso
    let Φ : (Multiplicative (ρbar.V × ρbar.V) →* (PadicAlgCl p)ˣ) →*
        (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ) :=
      MonoidHom.compHom' E.toMonoidHom
    have hΦ : ∀ χ₂ f, Φ χ₂ f = χ₂ (E f) := fun _ _ => rfl
    let 𝒦₂ : Subgroup (Multiplicative (ρbar.V × ρbar.V) →* (PadicAlgCl p)ˣ) := 𝒦.comap Φ
    have h𝒦₂ : 𝒦₂ ≠ ⊤ := by
      intro h2
      apply htop
      rw [eq_top_iff]
      intro χ _
      have hχ : χ = Φ (χ.comp E.symm.toMonoidHom) := by
        ext f
        rw [hΦ]
        simp
      have hmem : χ.comp E.symm.toMonoidHom ∈ 𝒦₂ := by rw [h2]; exact Subgroup.mem_top _
      rw [hχ]
      exact hmem
    haveI : Finite ρbar.V := Module.finite_of_finite k
    have hM : ∀ m : ρbar.V × ρbar.V, p • m = 0 := by
      intro m
      rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
    obtain ⟨hsep, hann⟩ :=
      MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
        p (ρbar.V × ρbar.V) hM (PadicAlgCl p)
    obtain ⟨m, hm0, hm⟩ := hann 𝒦₂ h𝒦₂

    have heval : ∀ (χ₂ : Multiplicative (ρbar.V × ρbar.V) →* (PadicAlgCl p)ˣ) (x : ρbar.V × ρbar.V),
        Φ χ₂ (pt x) = χ₂ (Multiplicative.ofAdd x) := by
      intro χ₂ x
      rw [hΦ]
      show χ₂ (E (E.symm (Multiplicative.ofAdd x))) = _
      rw [E.apply_symm_apply]

    have hkill : ∀ κ ∈ 𝒦, κ (pt m) = 1 := by
      intro κ hκ
      have h1 : κ = Φ (κ.comp E.symm.toMonoidHom) := by
        ext f
        rw [hΦ]
        simp
      have h2 : κ.comp E.symm.toMonoidHom ∈ 𝒦₂ := by
        show Φ (κ.comp E.symm.toMonoidHom) ∈ 𝒦
        rw [← h1]; exact hκ
      rw [h1, heval]
      exact hm _ h2

    have hstar : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ χ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ,
          (χ (pt m) : PadicAlgCl p) =
            ResidualGaloisRep.localAut p σ (χ (pt (ρbar.dualLiftModuleActAd p c σ⁻¹ m))) := by
      intro σ hσ χ
      obtain ⟨κ, hκ, hcos⟩ := hcoset σ hσ χ
      have hm' : pt m = gal σ (pt (ρbar.dualLiftModuleActAd p c σ⁻¹ m)) := by
        rw [← hpt_gal, hact_inv]
      have heq := hd_act (ResidualGaloisRep.localAut p σ) (d.symm χ) (gal' σ (d.symm χ))
        (hgal' σ (d.symm χ)) (pt (ρbar.dualLiftModuleActAd p c σ⁻¹ m)) (pt m) (by
          intro x
          rw [hm']
          rfl)
      rw [d.apply_symm_apply, hcos, MonoidHom.mul_apply, Units.val_mul, hkill κ hκ, Units.val_one,
        one_mul] at heq
      exact heq

    have hcoord : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ n : ℕ,
          (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ n) →
            ρbar.dualLiftModuleActAd p c σ m = (n : k) • m := by
      intro σ hσ n hn
      rw [Nat.cast_smul_eq_nsmul]
      apply sub_eq_zero.mp
      apply hsep
      intro χ₂
      have hσinv : ResidualGaloisRep.localAut p σ⁻¹ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] :=
        Subgroup.inv_mem _ hσ
      have h := hstar σ⁻¹ hσinv (Φ χ₂)
      rw [inv_inv] at h

      have h2 : ResidualGaloisRep.localAut p σ ((Φ χ₂) (pt m) : PadicAlgCl p) =
          ((Φ χ₂) (pt (ρbar.dualLiftModuleActAd p c σ m)) : PadicAlgCl p) := by
        rw [h]
        show (ResidualGaloisRep.localAut p σ) ((ResidualGaloisRep.localAut p σ)⁻¹ _) = _
        rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

      have hroot : (((Φ χ₂) (pt m) : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpt_nsmul, hM, ← Units.val_one]
        congr 1
        rw [heval, ofAdd_zero, map_one]
      rw [hn _ hroot, ← Units.val_pow_eq_pow_val, ← map_pow, ← hpt_nsmul, heval, heval] at h2
      have h3 := Units.val_injective h2
      rw [ofAdd_sub, map_div, div_eq_one]
      exact h3.symm
    have h1 : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ n : ℕ,
          (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ n) →
            ρ σ m.1 = (n : k) • m.1 := by
      intro σ hσ n hn
      have h := congrArg Prod.fst (hcoord σ hσ n hn)
      rw [Prod.smul_fst] at h
      exact h
    have hm1 : m.1 = 0 := noω m.1 h1
    have h2 : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → ∀ n : ℕ,
          (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → ResidualGaloisRep.localAut p σ ζ = ζ ^ n) →
            ρ σ m.2 = (n : k) • m.2 := by
      intro σ hσ n hn
      have h := congrArg Prod.snd (hcoord σ hσ n hn)
      rw [Prod.smul_snd] at h
      have h' : ((c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ) (ρ σ m.1) + ρ σ m.2
          = (n : k) • m.2 := h
      rwa [hm1, map_zero, map_zero, zero_add] at h'
    have hm2 : m.2 = 0 := noω m.2 h2
    exact hm0 (Prod.ext hm1 hm2)

end S17.ExtUnip

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
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p c σ (e f) :=
  S17.ExtUnip.main p hp2 hker ρbar hunip c hc

end S_ResidualGaloisRep_exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_ResidualGaloisRep_exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual (solution)
