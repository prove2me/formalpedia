-- Prove2me | solution 1 for PDivisibleGroup.cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/15b757c6-9fad-55af-80fc-046709b068fd

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_Bialgebra_exists_eq_comp_of_comp_eq_counit_of_ker_eq_map
import Theorems.Thm_HopfAlgebra_map_antipode_comul_of_isCocomm
import Theorems.Thm_HopfAlgebra_antipode_antipode
import Theorems.Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w x

namespace S42GAM

namespace Kit

section Frobenius

variable (p : ℕ) [Fact p.Prime]

def algHomOfRingHom {A B : Type*} [Ring A] [Ring B] [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (f : A →+* B) : A →ₐ[ZMod p] B :=
  { f with
    commutes' := fun c =>
      DFunLike.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod p) A)) (algebraMap (ZMod p) B)) c }

@[scoped simp] theorem algHomOfRingHom_apply {A B : Type*} [Ring A] [Ring B] [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (f : A →+* B) (a : A) : algHomOfRingHom p f a = f a := rfl

theorem nontrivial (B : Type*) [CommRing B] [Bialgebra (ZMod p) B] : Nontrivial B :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := ZMod p) (by
    have := congrArg (Coalgebra.counit (R := ZMod p) (A := B)) h
    rwa [map_zero, Bialgebra.counit_one] at this)⟩⟩

theorem charP (B : Type*) [CommRing B] [Bialgebra (ZMod p) B] : CharP B p :=
  haveI := nontrivial p B
  charP_of_injective_algebraMap (algebraMap (ZMod p) B).injective p

theorem expChar (B : Type*) [CommRing B] [Bialgebra (ZMod p) B] : ExpChar B p :=
  haveI := charP p B
  ExpChar.prime Fact.out

variable (B : Type*) [CommRing B] [Bialgebra (ZMod p) B]

noncomputable def frobAlgHom : B →ₐ[ZMod p] B :=
  haveI := expChar p B
  algHomOfRingHom p (frobenius B p)

theorem frobAlgHom_apply (x : B) : frobAlgHom p B x = x ^ p := by
  haveI := expChar p B
  show algHomOfRingHom p (frobenius B p) x = x ^ p
  rw [algHomOfRingHom_apply, frobenius_def]

variable {B}
variable {C : Type*} [CommRing C] [Bialgebra (ZMod p) C]

theorem comp_frobAlgHom {F : Type*} [FunLike F B C] [AlgHomClass F (ZMod p) B C] (f : F) (x : B) :
    f (frobAlgHom p B x) = frobAlgHom p C (f x) := by
  rw [frobAlgHom_apply, frobAlgHom_apply, map_pow]

theorem algHom_comp_frobAlgHom (f : B →ₐ[ZMod p] C) :
    f.comp (frobAlgHom p B) = (frobAlgHom p C).comp f :=
  AlgHom.ext fun x => comp_frobAlgHom p f x

variable (B)

theorem frobAlgHom_tensor (z : B ⊗[ZMod p] B) :
    frobAlgHom p (B ⊗[ZMod p] B) z = Algebra.TensorProduct.map (frobAlgHom p B) (frobAlgHom p B) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, frobAlgHom_apply, frobAlgHom_apply, frobAlgHom_apply,
      Algebra.TensorProduct.tmul_pow]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

noncomputable def frobBialgHom : B →ₐc[ZMod p] B :=
  BialgHom.ofAlgHom (frobAlgHom p B)
    (by
      refine AlgHom.ext fun x => ?_
      rw [AlgHom.comp_apply, comp_frobAlgHom p (Bialgebra.counitAlgHom (ZMod p) B) x, frobAlgHom_apply,
        ZMod.pow_card])
    (by
      refine AlgHom.ext fun x => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, comp_frobAlgHom p (Bialgebra.comulAlgHom (ZMod p) B) x,
        frobAlgHom_tensor])

theorem frobBialgHom_apply (x : B) : frobBialgHom p B x = x ^ p := frobAlgHom_apply p B x

theorem toAlgHom_frobBialgHom : (frobBialgHom p B : B →ₐ[ZMod p] B) = frobAlgHom p B := rfl

variable {B}

theorem bialgHom_comp_frobBialgHom (f : B →ₐc[ZMod p] C) :
    f.comp (frobBialgHom p B) = (frobBialgHom p C).comp f :=
  BialgHom.ext fun x => by
    show f (frobAlgHom p B x) = frobAlgHom p C (f x)
    exact comp_frobAlgHom p f x

end Frobenius
end Kit
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit"

section Generic

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [HopfAlgebra R B]

noncomputable def antipodeBialgHom [Coalgebra.IsCocomm R B] : B →ₐc[R] B :=
  BialgHom.ofAlgHom (PDivisibleGroup.Hopf.antipodeAlgHom R B)
    (by
      apply AlgHom.ext
      intro x
      show Coalgebra.counit (R := R) (HopfAlgebra.antipode R x) = Coalgebra.counit (R := R) x
      exact HopfAlgebra.counit_antipode x)
    (by
      apply AlgHom.ext
      intro x
      show Algebra.TensorProduct.map (PDivisibleGroup.Hopf.antipodeAlgHom R B) (PDivisibleGroup.Hopf.antipodeAlgHom R B)
          (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) (HopfAlgebra.antipode R x)
      rw [← HopfAlgebra.map_antipode_comul_of_isCocomm inferInstance x]
      induction Coalgebra.comul (R := R) x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul a b => rfl
      | add a b ha hb => rw [map_add, map_add, ha, hb])

@[scoped simp] theorem antipodeBialgHom_apply [Coalgebra.IsCocomm R B] (x : B) :
    antipodeBialgHom (R := R) (B := B) x = HopfAlgebra.antipode R x := rfl

noncomputable def cinv [Coalgebra.IsCocomm R B] (y : B →ₐc[R] B) : B →ₐc[R] B := y.comp antipodeBialgHom

theorem cinv_apply [Coalgebra.IsCocomm R B] (y : B →ₐc[R] B) (x : B) : cinv y x = y (HopfAlgebra.antipode R x) := rfl

theorem toAlgHom_cinv [Coalgebra.IsCocomm R B] (y : B →ₐc[R] B) :
    (cinv y : B →ₐ[R] B) = (y : B →ₐ[R] B).comp (PDivisibleGroup.Hopf.antipodeAlgHom R B) := rfl

theorem convMul_cinv [Coalgebra.IsCocomm R B] (y : B →ₐc[R] B) :
    WithConv.toConv (y : B →ₐ[R] B) * WithConv.toConv (cinv y : B →ₐ[R] B) = 1 := by
  rw [toAlgHom_cinv]
  exact PDivisibleGroup.Hopf.convMul_comp_antipodeAlgHom (y : B →ₐ[R] B)

theorem map_antipode {C : Type*} [CommRing C] [HopfAlgebra R C] (f : B →ₐc[R] C) (x : B) :
    f (HopfAlgebra.antipode R x) = HopfAlgebra.antipode R (f x) := by
  let u : B →ₐ[R] C := (f : B →ₐ[R] C).comp (PDivisibleGroup.Hopf.antipodeAlgHom R B)
  let w : B →ₐ[R] C := (PDivisibleGroup.Hopf.antipodeAlgHom R C).comp (f : B →ₐ[R] C)
  have hu : WithConv.toConv (f : B →ₐ[R] C) * WithConv.toConv u = 1 :=
    PDivisibleGroup.Hopf.convMul_comp_antipodeAlgHom (f : B →ₐ[R] C)
  have hw : WithConv.toConv w * WithConv.toConv (f : B →ₐ[R] C) = 1 := by
    have h1 : WithConv.toConv (PDivisibleGroup.Hopf.antipodeAlgHom R C) * WithConv.toConv (AlgHom.id R C) = 1 :=
      PDivisibleGroup.Hopf.comp_antipodeAlgHom_convMul (AlgHom.id R C)
    have h2 := AlgHom.convMul_comp_bialgHom_distrib (WithConv.toConv (PDivisibleGroup.Hopf.antipodeAlgHom R C))
      (WithConv.toConv (AlgHom.id R C)) f
    rw [h1] at h2

    have h3 : (WithConv.ofConv (1 : WithConv (C →ₐ[R] C))).comp (f : B →ₐ[R] C) =
        WithConv.ofConv (1 : WithConv (B →ₐ[R] C)) := by
      apply AlgHom.ext
      intro b
      show algebraMap R C (Coalgebra.counit (R := R) (f b)) = algebraMap R C (Coalgebra.counit (R := R) b)
      rw [CoalgHomClass.counit_comp_apply]
    rw [h3, AlgHom.id_comp] at h2
    have h4 := congrArg WithConv.toConv h2
    rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv] at h4
    exact h4.symm
  have huw : w = u := by
    have := left_inv_eq_right_inv hw hu
    exact WithConv.toConv_injective this
  exact (AlgHom.congr_fun huw x).symm

theorem dualDistrib_map_map [Module.Finite R B] [Module.Free R B]
    (u w : B →ₐc[R] B) (z : CartierDual R B ⊗[R] CartierDual R B) (t : B ⊗[R] B) :
    TensorProduct.dualDistrib R B B
        (TensorProduct.map (CartierDual.toDual R B).toLinearMap (CartierDual.toDual R B).toLinearMap
          (TensorProduct.map (CartierDual.map u : CartierDual R B →ₗ[R] CartierDual R B)
            (CartierDual.map w : CartierDual R B →ₗ[R] CartierDual R B) z)) t =
      TensorProduct.dualDistrib R B B
        (TensorProduct.map (CartierDual.toDual R B).toLinearMap (CartierDual.toDual R B).toLinearMap z)
        (TensorProduct.map (u : B →ₐ[R] B).toLinearMap (w : B →ₐ[R] B).toLinearMap t) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul ψ₁ ψ₂ =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rfl
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

theorem dualDistrib_comul_eq [Module.Finite R B] [Module.Free R B] (ψ : CartierDual R B) (t : B ⊗[R] B) :
    TensorProduct.dualDistrib R B B
        (TensorProduct.map (CartierDual.toDual R B).toLinearMap (CartierDual.toDual R B).toLinearMap (Coalgebra.comul (R := R) ψ)) t =
      ψ (LinearMap.mul' R B t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [CartierDual.comul_pairing, LinearMap.mul'_apply]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem map_toLinearMap_convMul [Coalgebra.IsCocomm R B] [Module.Finite R B] [Module.Free R B]
    (u w : B →ₐc[R] B) (ψ : CartierDual R B) (b : B) :
    ψ ((WithConv.toConv (u : B →ₐ[R] B) * WithConv.toConv (w : B →ₐ[R] B)).ofConv b) =
      ((WithConv.toConv (CartierDual.map u : CartierDual R B →ₗ[R] CartierDual R B) *
        WithConv.toConv (CartierDual.map w : CartierDual R B →ₗ[R] CartierDual R B)).ofConv ψ) b := by

  rw [LinearMap.convMul_apply]
  have hm : ∀ Z : CartierDual R B ⊗[R] CartierDual R B, (LinearMap.mul' R (CartierDual R B) Z) b =
      TensorProduct.dualDistrib R B B
        (TensorProduct.map (CartierDual.toDual R B).toLinearMap (CartierDual.toDual R B).toLinearMap Z)
        (Coalgebra.comul (R := R) b) := by
    intro Z
    induction Z using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]; rfl
    | tmul χ₁ χ₂ => rw [LinearMap.mul'_apply, CartierDual.mul_apply]; rfl
    | add a c ha hc =>
      rw [map_add, map_add, map_add, LinearMap.add_apply, ← ha, ← hc]
      rfl
  erw [hm, dualDistrib_map_map u w (Coalgebra.comul (R := R) ψ) (Coalgebra.comul (R := R) b), dualDistrib_comul_eq]

  rw [AlgHom.convMul_apply]
  congr 1
  induction Coalgebra.comul (R := R) b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

end Generic
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit"

section Engine

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 3200000 in

theorem engineM
    {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] [Module.Free (ZMod p) B]
    (f : B →ₐc[ZMod p] B) (dd : B ≃ₐc[ZMod p] B)
    {G₁ : Type v} [CommRing G₁] [HopfAlgebra (ZMod p) G₁] [Coalgebra.IsCocomm (ZMod p) G₁]
    [Module.Finite (ZMod p) G₁] [Module.Free (ZMod p) G₁]
    (π : B →ₐc[ZMod p] G₁) (hπ : Function.Surjective π)
    {G₂ : Type w} [CommRing G₂] [HopfAlgebra (ZMod p) G₂] [Coalgebra.IsCocomm (ZMod p) G₂]
    [Module.Finite (ZMod p) G₂] [Module.Free (ZMod p) G₂]
    (jq : G₂ →ₐc[ZMod p] B)
    (hex : RingHom.ker (π : B →ₐ[ZMod p] G₁) =
      Ideal.map (jq : G₂ →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) G₂)))
    (φ₁ : G₁ →ₐc[ZMod p] G₁) (φ₂ : G₂ →ₐc[ZMod p] G₂) (d₂ : G₂ ≃ₐc[ZMod p] G₂)
    (hπφ : π.comp f = φ₁.comp π) (hjφ : f.comp jq = jq.comp φ₂)
    (hjD : (dd : B →ₐc[ZMod p] B).comp jq = jq.comp (d₂ : G₂ →ₐc[ZMod p] G₂))
    (Ver₁ : G₁ →ₐc[ZMod p] G₁) (hVer₁ : ∀ ψ : CartierDual (ZMod p) G₁, CartierDual.map Ver₁ ψ = ψ ^ p)
    (hE1 : φ₁ = Ver₁)
    (hE2 : ∀ x : G₂, φ₂ x = d₂ (x ^ p))
    :
    ∃ Vr : B →ₐc[ZMod p] B,
      (∀ a, (Vr a) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) B p a) ∧
      (∀ a, Vr (a ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) B p a) ∧
      (∀ (ψ : CartierDual (ZMod p) B) (a : B), ψ (Vr a) = (ψ ^ p) a) ∧
      (((WithConv.toConv f * WithConv.toConv (cinv ((dd : B →ₐc[ZMod p] B).comp (Kit.frobBialgHom p B)))).ofConv :
          B →ₐc[ZMod p] B) : B →ₐ[ZMod p] B).comp
        (((WithConv.toConv f * WithConv.toConv (cinv Vr)).ofConv : B →ₐc[ZMod p] B) : B →ₐ[ZMod p] B) =
        WithConv.ofConv (1 : WithConv (B →ₐ[ZMod p] B)) := by
  classical

  obtain ⟨Vr, hVrp, hVrp', hVrdual⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p B

  have hVπ : ∀ b : B, π (Vr b) = Ver₁ (π b) := by
    intro b
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod p)]
    intro ψ'
    let ψ : CartierDual (ZMod p) G₁ := ψ'
    have h1 : ψ (π (Vr b)) = ((CartierDual.map π ψ) ^ p) b := by
      rw [← CartierDual.map_apply π ψ, hVrdual]
    have h2 : ψ (Ver₁ (π b)) = ((CartierDual.map π ψ) ^ p) b := by
      rw [← CartierDual.map_apply Ver₁ ψ, hVer₁, ← map_pow, CartierDual.map_apply]
    show ψ (π (Vr b) - Ver₁ (π b)) = 0
    rw [map_sub, h1, h2, sub_self]

  let Fr : B →ₐc[ZMod p] B := Kit.frobBialgHom p B
  have hFr : ∀ x, Fr x = x ^ p := Kit.frobBialgHom_apply p B
  have hφ₂ : φ₂ = (d₂ : G₂ →ₐc[ZMod p] G₂).comp (Kit.frobBialgHom p G₂) :=
    BialgHom.ext fun x => (hE2 x).trans (by rw [BialgHom.comp_apply, Kit.frobBialgHom_apply]; rfl)

  let VD : B →ₐc[ZMod p] B := (dd : B →ₐc[ZMod p] B).comp Fr
  have hVDjq : VD.comp jq = jq.comp φ₂ := by
    apply BialgHom.ext
    intro g
    show dd (Fr (jq g)) = jq (φ₂ g)
    rw [hFr, ← map_pow, hφ₂, BialgHom.comp_apply, Kit.frobBialgHom_apply]
    exact DFunLike.congr_fun hjD (g ^ p)

  let x : B →ₐc[ZMod p] B := (WithConv.toConv f * WithConv.toConv (cinv VD)).ofConv
  have hx_alg : (x : B →ₐ[ZMod p] B) =
      (WithConv.toConv (f : B →ₐ[ZMod p] B) * WithConv.toConv (cinv VD : B →ₐ[ZMod p] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv f) (WithConv.toConv (cinv VD)))
  have hx : (x : B →ₐ[ZMod p] B).comp (jq : G₂ →ₐ[ZMod p] B) =
      (Algebra.ofId (ZMod p) B).comp (Bialgebra.counitAlgHom (ZMod p) G₂) := by
    rw [hx_alg, AlgHom.convMul_comp_bialgHom_distrib]
    have h1 : (f : B →ₐ[ZMod p] B).comp (jq : G₂ →ₐ[ZMod p] B) = (jq : G₂ →ₐ[ZMod p] B).comp (φ₂ : G₂ →ₐ[ZMod p] G₂) :=
      congrArg BialgHom.toAlgHom hjφ
    have h2 : (cinv VD : B →ₐ[ZMod p] B).comp (jq : G₂ →ₐ[ZMod p] B) =
        (jq : G₂ →ₐ[ZMod p] B).comp ((φ₂ : G₂ →ₐ[ZMod p] G₂).comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) G₂)) := by
      apply AlgHom.ext
      intro g
      show VD (HopfAlgebra.antipode (ZMod p) (jq g)) = jq (φ₂ (HopfAlgebra.antipode (ZMod p) g))
      rw [← map_antipode jq g, ← BialgHom.comp_apply VD jq, hVDjq, BialgHom.comp_apply, map_antipode φ₂ g]
    rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, h1, h2, ← AlgHom.comp_convMul_distrib,
      PDivisibleGroup.Hopf.convMul_comp_antipodeAlgHom]
    apply AlgHom.ext
    intro g
    show jq (algebraMap (ZMod p) G₂ (Coalgebra.counit (R := ZMod p) g)) = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) g)
    rw [AlgHomClass.commutes]

  obtain ⟨y, hy⟩ := Bialgebra.exists_eq_comp_of_comp_eq_counit_of_ker_eq_map π hπ jq hex x hx

  let gg : B →ₐc[ZMod p] B := (WithConv.toConv f * WithConv.toConv (cinv Vr)).ofConv
  have hgg_alg : (gg : B →ₐ[ZMod p] B) =
      (WithConv.toConv (f : B →ₐ[ZMod p] B) * WithConv.toConv (cinv Vr : B →ₐ[ZMod p] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv f) (WithConv.toConv (cinv Vr)))
  have one_comp : ∀ (φ' : B →ₐc[ZMod p] B),
      (WithConv.ofConv (1 : WithConv (B →ₐ[ZMod p] B))).comp (φ' : B →ₐ[ZMod p] B) =
        WithConv.ofConv (1 : WithConv (B →ₐ[ZMod p] B)) := by
    intro φ'
    apply AlgHom.ext
    intro b
    show algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) (φ' b)) = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) b)
    rw [CoalgHomClass.counit_comp_apply]
  have hπg : (π : B →ₐ[ZMod p] G₁).comp (gg : B →ₐ[ZMod p] B) =
      ((WithConv.ofConv (1 : WithConv (B →ₐ[ZMod p] G₁))) : B →ₐ[ZMod p] G₁) := by
    rw [hgg_alg, AlgHom.comp_convMul_distrib]
    have h1 : (π : B →ₐ[ZMod p] G₁).comp (f : B →ₐ[ZMod p] B) =
        (Ver₁ : G₁ →ₐ[ZMod p] G₁).comp (π : B →ₐ[ZMod p] G₁) := by
      rw [← hE1]; exact congrArg BialgHom.toAlgHom hπφ
    have h2 : (π : B →ₐ[ZMod p] G₁).comp (cinv Vr : B →ₐ[ZMod p] B) =
        ((Ver₁ : G₁ →ₐ[ZMod p] G₁).comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) G₁)).comp (π : B →ₐ[ZMod p] G₁) := by
      apply AlgHom.ext
      intro b
      show π (Vr (HopfAlgebra.antipode (ZMod p) b)) = Ver₁ (HopfAlgebra.antipode (ZMod p) (π b))
      rw [hVπ, map_antipode π]
    rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, h1, h2]
    have h5 := AlgHom.convMul_comp_bialgHom_distrib (WithConv.toConv (Ver₁ : G₁ →ₐ[ZMod p] G₁))
      (WithConv.toConv ((Ver₁ : G₁ →ₐ[ZMod p] G₁).comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) G₁))) π
    rw [PDivisibleGroup.Hopf.convMul_comp_antipodeAlgHom, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h5
    rw [← h5]
    apply AlgHom.ext
    intro b
    show algebraMap (ZMod p) G₁ (Coalgebra.counit (R := ZMod p) (π b)) = algebraMap (ZMod p) G₁ (Coalgebra.counit (R := ZMod p) b)
    rw [CoalgHomClass.counit_comp_apply]

  have hxg : (x : B →ₐ[ZMod p] B).comp (gg : B →ₐ[ZMod p] B) = WithConv.ofConv (1 : WithConv (B →ₐ[ZMod p] B)) := by
    rw [show (x : B →ₐ[ZMod p] B) = (y : G₁ →ₐ[ZMod p] B).comp (π : B →ₐ[ZMod p] G₁) from congrArg BialgHom.toAlgHom hy,
      AlgHom.comp_assoc, hπg]
    apply AlgHom.ext
    intro b
    show y (algebraMap (ZMod p) G₁ (Coalgebra.counit (R := ZMod p) b)) = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) b)
    rw [AlgHomClass.commutes]
  exact ⟨Vr, hVrp, hVrp', hVrdual, hxg⟩

end Engine
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit"

section CoreG

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 6400000 in
theorem coreG
    {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] [Module.Free (ZMod p) B]
    (f : B →ₐc[ZMod p] B) (dd : B ≃ₐc[ZMod p] B)

    {T : Type v} [CommRing T] [HopfAlgebra (ZMod p) T] [Coalgebra.IsCocomm (ZMod p) T]
    [Module.Finite (ZMod p) T] [Module.Free (ZMod p) T]
    (πT : B →ₐc[ZMod p] T) (hπT : Function.Surjective πT)
    (VerT : T ≃ₐc[ZMod p] T) (hVerT : ∀ ψ : CartierDual (ZMod p) T, CartierDual.map (VerT : T →ₐc[ZMod p] T) ψ = ψ ^ p)

    {C : Type w} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C]
    [Module.Finite (ZMod p) C] [Module.Free (ZMod p) C]
    (jB : C →ₐc[ZMod p] B)
    (hexT : RingHom.ker (πT : B →ₐ[ZMod p] T) =
      Ideal.map (jB : C →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) C)))
    (fC : C →ₐc[ZMod p] C) (ddC : C ≃ₐc[ZMod p] C)
    (hjBφ : f.comp jB = jB.comp fC) (hjBD : (dd : B →ₐc[ZMod p] B).comp jB = jB.comp (ddC : C →ₐc[ZMod p] C))

    {G₁ : Type x} [CommRing G₁] [HopfAlgebra (ZMod p) G₁] [Coalgebra.IsCocomm (ZMod p) G₁]
    [Module.Finite (ZMod p) G₁] [Module.Free (ZMod p) G₁]
    (π : C →ₐc[ZMod p] G₁) (hπ : Function.Surjective π)
    {G₂ : Type x} [CommRing G₂] [HopfAlgebra (ZMod p) G₂] [Coalgebra.IsCocomm (ZMod p) G₂]
    [Module.Finite (ZMod p) G₂] [Module.Free (ZMod p) G₂]
    (jq : G₂ →ₐc[ZMod p] C)
    (hex : RingHom.ker (π : C →ₐ[ZMod p] G₁) =
      Ideal.map (jq : G₂ →ₐ[ZMod p] C) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) G₂)))
    (φ₁ : G₁ →ₐc[ZMod p] G₁) (φ₂ : G₂ →ₐc[ZMod p] G₂) (d₂ : G₂ ≃ₐc[ZMod p] G₂)
    (hπφ : π.comp fC = φ₁.comp π) (hjφ : fC.comp jq = jq.comp φ₂)
    (hjD : (ddC : C →ₐc[ZMod p] C).comp jq = jq.comp (d₂ : G₂ →ₐc[ZMod p] G₂))
    (Ver₁ : G₁ →ₐc[ZMod p] G₁) (hVer₁ : ∀ ψ : CartierDual (ZMod p) G₁, CartierDual.map Ver₁ ψ = ψ ^ p)
    (hE1 : φ₁ = Ver₁)
    (hE2 : ∀ x : G₂, φ₂ x = d₂ (x ^ p))
    (Fk : B →ₐc[ZMod p] B) (hFk : ∀ x, Fk x = x ^ p)
    (FD : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) (hFD : ∀ ψ, FD ψ = ψ ^ p) :
    ∃ (a b : CartierDual (ZMod p) B →ₐc[ZMod p] CartierDual (ZMod p) B),
      (CartierDual.map f : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ^ 2 =
        (WithConv.toConv ((FD : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
            (a : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) *
          WithConv.toConv ((b : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
            (CartierDual.map Fk : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B))).ofConv := by
  classical

  obtain ⟨VrC, hVCp, hVCp', hVCdual, hxgC⟩ :=
    engineM p fC ddC π hπ jq hex φ₁ φ₂ d₂ hπφ hjφ hjD Ver₁ hVer₁ hE1 hE2

  obtain ⟨Vr, hVrp, hVrp', hVrdual⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p B

  have hVjB : ∀ c : C, Vr (jB c) = jB (VrC c) := by
    intro c
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod p)]
    intro ψ'
    let ψ : CartierDual (ZMod p) B := ψ'
    have h1 : ψ (Vr (jB c)) = (ψ ^ p) (jB c) := hVrdual ψ (jB c)
    have h2 : ψ (jB (VrC c)) = (ψ ^ p) (jB c) := by
      rw [← CartierDual.map_apply jB ψ, hVCdual, ← map_pow, CartierDual.map_apply]
    show ψ (Vr (jB c) - jB (VrC c)) = 0
    rw [map_sub, h1, h2, sub_self]
  have hVπT : ∀ b : B, πT (Vr b) = VerT (πT b) := by
    intro b
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (ZMod p)]
    intro ψ'
    let ψ : CartierDual (ZMod p) T := ψ'
    have h1 : ψ (πT (Vr b)) = ((CartierDual.map πT ψ) ^ p) b := by
      rw [← CartierDual.map_apply πT ψ, hVrdual]
    have h2 : ψ (VerT (πT b)) = ((CartierDual.map πT ψ) ^ p) b := by
      rw [← map_pow, CartierDual.map_apply, ← hVerT, CartierDual.map_apply]
      rfl
    show ψ (πT (Vr b) - VerT (πT b)) = 0
    rw [map_sub, h1, h2, sub_self]

  let Fr : B →ₐc[ZMod p] B := Kit.frobBialgHom p B
  have hFr : ∀ x, Fr x = x ^ p := Kit.frobBialgHom_apply p B
  have hFk' : Fk = Fr := BialgHom.ext fun x => (hFk x).trans (hFr x).symm
  let hh : B →ₐc[ZMod p] B := (dd : B →ₐc[ZMod p] B).comp Fr
  let hC : C →ₐc[ZMod p] C := (ddC : C →ₐc[ZMod p] C).comp (Kit.frobBialgHom p C)
  have hhjB : hh.comp jB = jB.comp hC := by
    apply BialgHom.ext
    intro c
    show dd (Fr (jB c)) = jB (ddC (c ^ p))
    rw [hFr, ← map_pow]
    exact DFunLike.congr_fun hjBD (c ^ p)

  let x : B →ₐc[ZMod p] B := (WithConv.toConv f * WithConv.toConv (cinv hh)).ofConv
  let g : B →ₐc[ZMod p] B := (WithConv.toConv f * WithConv.toConv (cinv Vr)).ofConv
  let xC : C →ₐc[ZMod p] C := (WithConv.toConv fC * WithConv.toConv (cinv hC)).ofConv
  let gC : C →ₐc[ZMod p] C := (WithConv.toConv fC * WithConv.toConv (cinv VrC)).ofConv
  have hx_alg : (x : B →ₐ[ZMod p] B) =
      (WithConv.toConv (f : B →ₐ[ZMod p] B) * WithConv.toConv (cinv hh : B →ₐ[ZMod p] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv f) (WithConv.toConv (cinv hh)))
  have hg_alg : (g : B →ₐ[ZMod p] B) =
      (WithConv.toConv (f : B →ₐ[ZMod p] B) * WithConv.toConv (cinv Vr : B →ₐ[ZMod p] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv f) (WithConv.toConv (cinv Vr)))
  have hxC_alg : (xC : C →ₐ[ZMod p] C) =
      (WithConv.toConv (fC : C →ₐ[ZMod p] C) * WithConv.toConv (cinv hC : C →ₐ[ZMod p] C)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv fC) (WithConv.toConv (cinv hC)))
  have hgC_alg : (gC : C →ₐ[ZMod p] C) =
      (WithConv.toConv (fC : C →ₐ[ZMod p] C) * WithConv.toConv (cinv VrC : C →ₐ[ZMod p] C)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv fC) (WithConv.toConv (cinv VrC)))

  have restr : ∀ (u w : B →ₐc[ZMod p] B) (uC wC : C →ₐc[ZMod p] C),
      u.comp jB = jB.comp uC → w.comp jB = jB.comp wC →
      ((WithConv.toConv (u : B →ₐ[ZMod p] B) * WithConv.toConv (cinv w : B →ₐ[ZMod p] B)).ofConv).comp (jB : C →ₐ[ZMod p] B) =
        (jB : C →ₐ[ZMod p] B).comp
          (WithConv.toConv (uC : C →ₐ[ZMod p] C) * WithConv.toConv (cinv wC : C →ₐ[ZMod p] C)).ofConv := by
    intro u w uC wC hu hw
    rw [AlgHom.convMul_comp_bialgHom_distrib, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
      WithConv.ofConv_toConv, WithConv.ofConv_toConv]
    have e1 : (u : B →ₐ[ZMod p] B).comp (jB : C →ₐ[ZMod p] B) = (jB : C →ₐ[ZMod p] B).comp (uC : C →ₐ[ZMod p] C) :=
      congrArg BialgHom.toAlgHom hu
    have e2 : (cinv w : B →ₐ[ZMod p] B).comp (jB : C →ₐ[ZMod p] B) = (jB : C →ₐ[ZMod p] B).comp (cinv wC : C →ₐ[ZMod p] C) := by
      apply AlgHom.ext
      intro c
      show w (HopfAlgebra.antipode (ZMod p) (jB c)) = jB (wC (HopfAlgebra.antipode (ZMod p) c))
      rw [← map_antipode jB c]
      exact DFunLike.congr_fun hw (HopfAlgebra.antipode (ZMod p) c)
    rw [e1, e2]
  have hxjB : (x : B →ₐ[ZMod p] B).comp (jB : C →ₐ[ZMod p] B) = (jB : C →ₐ[ZMod p] B).comp (xC : C →ₐ[ZMod p] C) := by
    rw [hx_alg, hxC_alg]; exact restr f hh fC hC hjBφ hhjB
  have hgjB : (g : B →ₐ[ZMod p] B).comp (jB : C →ₐ[ZMod p] B) = (jB : C →ₐ[ZMod p] B).comp (gC : C →ₐ[ZMod p] C) := by
    rw [hg_alg, hgC_alg]; exact restr f Vr fC VrC hjBφ (BialgHom.ext fun c => hVjB c)

  have hxgC' : (xC : C →ₐ[ZMod p] C).comp (gC : C →ₐ[ZMod p] C) = WithConv.ofConv (1 : WithConv (C →ₐ[ZMod p] C)) := hxgC
  have hz : ((x.comp g : B →ₐc[ZMod p] B) : B →ₐ[ZMod p] B).comp (jB : C →ₐ[ZMod p] B) =
      (Algebra.ofId (ZMod p) B).comp (Bialgebra.counitAlgHom (ZMod p) C) := by
    show ((x : B →ₐ[ZMod p] B).comp (g : B →ₐ[ZMod p] B)).comp (jB : C →ₐ[ZMod p] B) = _
    rw [AlgHom.comp_assoc, hgjB, ← AlgHom.comp_assoc, hxjB, AlgHom.comp_assoc, hxgC']
    apply AlgHom.ext
    intro c
    show jB (algebraMap (ZMod p) C (Coalgebra.counit (R := ZMod p) c)) = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) c)
    rw [AlgHomClass.commutes]

  obtain ⟨y, hy⟩ := Bialgebra.exists_eq_comp_of_comp_eq_counit_of_ker_eq_map πT hπT jB hexT (x.comp g) hz
  let cc : B →ₐc[ZMod p] B := (y.comp (VerT.symm : T →ₐc[ZMod p] T)).comp πT
  have hzc : (x : B →ₐ[ZMod p] B).comp (g : B →ₐ[ZMod p] B) = (cc : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B) := by
    have e1 : (x : B →ₐ[ZMod p] B).comp (g : B →ₐ[ZMod p] B) = ((y.comp πT : B →ₐc[ZMod p] B) : B →ₐ[ZMod p] B) :=
      congrArg BialgHom.toAlgHom hy
    rw [e1]
    apply AlgHom.ext
    intro b
    show y (πT b) = y (VerT.symm (πT (Vr b)))
    rw [hVπT, BialgEquiv.symm_apply_apply]

  have hexp : WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) *
      (WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)) *
        (WithConv.toConv ((cinv hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) *
          WithConv.toConv ((cinv hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)))) =
      WithConv.toConv ((cc : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) := by
    have h1 := hzc
    rw [hx_alg, AlgHom.convMul_comp_bialgHom_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hg_alg,
      AlgHom.comp_convMul_distrib, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h1
    have h2 := congrArg WithConv.toConv h1
    simp only [WithConv.toConv_ofConv] at h2
    rw [← h2]
    simp only [mul_assoc]

  have inv_of : ∀ z : B →ₐ[ZMod p] B,
      WithConv.toConv z * WithConv.toConv (z.comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) B)) = 1 :=
    fun z => PDivisibleGroup.Hopf.convMul_comp_antipodeAlgHom z
  have hSS : ∀ b : B, HopfAlgebra.antipode (ZMod p) (HopfAlgebra.antipode (ZMod p) b) = b :=
    fun b => HopfAlgebra.antipode_antipode b
  have i1 : ((f : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)).comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) B) =
      (f : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B) := by
    apply AlgHom.ext
    intro b
    show f (Vr (HopfAlgebra.antipode (ZMod p) (HopfAlgebra.antipode (ZMod p) b))) = f (Vr b)
    rw [hSS]
  have i2 : ((cinv hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)).comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) B) =
      (hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B) := by
    apply AlgHom.ext
    intro b
    show hh (HopfAlgebra.antipode (ZMod p) (f (HopfAlgebra.antipode (ZMod p) b))) = hh (f b)
    rw [map_antipode f, hSS]
  have i3 : ((cinv hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)).comp (PDivisibleGroup.Hopf.antipodeAlgHom (ZMod p) B) =
      (hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B) := by
    apply AlgHom.ext
    intro b
    show hh (HopfAlgebra.antipode (ZMod p) (Vr (HopfAlgebra.antipode (ZMod p) (HopfAlgebra.antipode (ZMod p) b)))) =
      hh (Vr (HopfAlgebra.antipode (ZMod p) b))
    rw [hSS, map_antipode Vr]

  have hZ : (WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)) *
      (WithConv.toConv ((cinv hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) *
        WithConv.toConv ((cinv hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)))) *
      (WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) *
        (WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) *
          WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)))) = 1 := by
    rw [← i1, ← i2, ← i3, mul_mul_mul_comm, inv_of, one_mul, mul_mul_mul_comm, inv_of, inv_of, one_mul]

  have hff : WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) =
      WithConv.toConv ((cc : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) *
        (WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) *
          (WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) *
            WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)))) := by
    rw [← hexp, mul_assoc, hZ, mul_one]

  have hgrp1 : WithConv.toConv ((cc : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) *
      WithConv.toConv ((f : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) =
      WithConv.toConv (((WithConv.toConv (cc : B →ₐ[ZMod p] B) * WithConv.toConv (f : B →ₐ[ZMod p] B)).ofConv).comp
        (Vr : B →ₐ[ZMod p] B)) := by
    rw [AlgHom.convMul_comp_bialgHom_distrib, WithConv.toConv_ofConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
  have hgrp2 : WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (f : B →ₐ[ZMod p] B)) *
      WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (cinv Vr : B →ₐ[ZMod p] B)) =
      WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (g : B →ₐ[ZMod p] B)) := by
    rw [hg_alg, AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
  rw [← mul_assoc, hgrp1, hgrp2] at hff

  let cf : B →ₐc[ZMod p] B := (WithConv.toConv cc * WithConv.toConv f).ofConv
  have hcf_alg : (cf : B →ₐ[ZMod p] B) = (WithConv.toConv (cc : B →ₐ[ZMod p] B) * WithConv.toConv (f : B →ₐ[ZMod p] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv cc) (WithConv.toConv f))
  have hffB : f.comp f = (WithConv.toConv (cf.comp Vr) * WithConv.toConv (hh.comp g)).ofConv := by
    apply BialgHom.coe_algHom_injective
    rw [show ((WithConv.toConv (cf.comp Vr) * WithConv.toConv (hh.comp g)).ofConv : B →ₐ[ZMod p] B) =
        (WithConv.toConv ((cf : B →ₐ[ZMod p] B).comp (Vr : B →ₐ[ZMod p] B)) *
          WithConv.toConv ((hh : B →ₐ[ZMod p] B).comp (g : B →ₐ[ZMod p] B))).ofConv from
      congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul _ _), hcf_alg]
    exact congrArg WithConv.ofConv hff

  refine ⟨CartierDual.map cf, CartierDual.map ((dd : B →ₐc[ZMod p] B).comp g), ?_⟩
  have hmapV : (CartierDual.map Vr : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) =
      (FD : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) := by
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro b
    show (CartierDual.map Vr ψ) b = (FD ψ) b
    rw [CartierDual.map_apply, hVrdual, hFD]
  have hlin_comp : ∀ (u w : B →ₐc[ZMod p] B),
      (CartierDual.map (u.comp w) : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) =
        (CartierDual.map w : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
          (CartierDual.map u : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) := by
    intro u w
    rw [CartierDual.map_comp]
    rfl
  have hlin_conv : ∀ (u w : B →ₐc[ZMod p] B),
      (CartierDual.map ((WithConv.toConv u * WithConv.toConv w).ofConv) :
          CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) =
        (WithConv.toConv (CartierDual.map u : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) *
          WithConv.toConv (CartierDual.map w : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)).ofConv := by
    intro u w
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro b
    show (CartierDual.map ((WithConv.toConv u * WithConv.toConv w).ofConv) ψ) b = _
    rw [CartierDual.map_apply]
    refine (congrArg ψ ?_).trans (map_toLinearMap_convMul u w ψ b)
    exact DFunLike.congr_fun (congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv u) (WithConv.toConv w))) b
  have hsq : (CartierDual.map f : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ^ 2 =
      (CartierDual.map (f.comp f) : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) := by
    rw [pow_two, Module.End.mul_eq_comp, hlin_comp]
  have hFrdd : (dd : B →ₐc[ZMod p] B).comp Fr = Fr.comp (dd : B →ₐc[ZMod p] B) := Kit.bialgHom_comp_frobBialgHom p (dd : B →ₐc[ZMod p] B)
  rw [hsq, hffB, hlin_conv, hlin_comp, hmapV, hlin_comp, show (CartierDual.map hh : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) =
      (CartierDual.map (dd : B →ₐc[ZMod p] B) : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (CartierDual.map Fr : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) from by
      show (CartierDual.map ((dd : B →ₐc[ZMod p] B).comp Fr) : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) = _
      rw [hFrdd, hlin_comp],
    ← LinearMap.comp_assoc, ← hlin_comp (dd : B →ₐc[ZMod p] B) g, hFk']

end CoreG
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit"

namespace BC
section BaseChangeFunctoriality

variable {R : Type*} [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
variable {X Y Z : Type*} [CommRing X] [Bialgebra R X] [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

theorem map_id_comp (a : Y →ₐc[R] Z) (b : X →ₐc[R] Y) :
    Bialgebra.TensorProduct.map (BialgHom.id k k) (a.comp b) =
      (Bialgebra.TensorProduct.map (BialgHom.id k k) a).comp (Bialgebra.TensorProduct.map (BialgHom.id k k) b) := by
  refine BialgHom.coe_algHom_injective (Algebra.TensorProduct.ext' fun c x => ?_)
  change Bialgebra.TensorProduct.map (BialgHom.id k k) (a.comp b) (c ⊗ₜ[R] x) =
    Bialgebra.TensorProduct.map (BialgHom.id k k) a (Bialgebra.TensorProduct.map (BialgHom.id k k) b (c ⊗ₜ[R] x))
  rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul]
  rfl

theorem map_id_id :
    Bialgebra.TensorProduct.map (BialgHom.id k k) (BialgHom.id R X) = BialgHom.id k (k ⊗[R] X) := by
  refine BialgHom.coe_algHom_injective (Algebra.TensorProduct.ext' fun c x => ?_)
  change Bialgebra.TensorProduct.map (BialgHom.id k k) (BialgHom.id R X) (c ⊗ₜ[R] x) = c ⊗ₜ[R] x
  rw [Bialgebra.TensorProduct.map_tmul]
  rfl

noncomputable def baseChangeEquiv (ψ : X ≃ₐc[R] Y) : k ⊗[R] X ≃ₐc[k] k ⊗[R] Y :=
  BialgEquiv.ofBijective (Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ : X →ₐc[R] Y))
    (by
      constructor
      ·
        refine Function.LeftInverse.injective
          (g := Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ.symm : Y →ₐc[R] X)) fun z => ?_
        change ((Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ.symm : Y →ₐc[R] X)).comp
          (Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ : X →ₐc[R] Y))) z = z
        rw [← map_id_comp]
        have : (ψ.symm : Y →ₐc[R] X).comp (ψ : X →ₐc[R] Y) = BialgHom.id R X := by
          refine BialgHom.ext fun x => ?_
          exact ψ.symm_apply_apply x
        rw [this, map_id_id]
        rfl
      · refine Function.RightInverse.surjective
          (g := Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ.symm : Y →ₐc[R] X)) fun z => ?_
        change ((Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ : X →ₐc[R] Y)).comp
          (Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ.symm : Y →ₐc[R] X))) z = z
        rw [← map_id_comp]
        have : (ψ : X →ₐc[R] Y).comp (ψ.symm : Y →ₐc[R] X) = BialgHom.id R Y := by
          refine BialgHom.ext fun y => ?_
          exact ψ.apply_symm_apply y
        rw [this, map_id_id]
        rfl)

theorem baseChangeEquiv_toBialgHom (ψ : X ≃ₐc[R] Y) :
    (baseChangeEquiv k ψ : k ⊗[R] X →ₐc[k] k ⊗[R] Y) =
      Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ : X →ₐc[R] Y) := rfl

theorem baseChangeEquiv_apply (ψ : X ≃ₐc[R] Y) (z : k ⊗[R] X) :
    baseChangeEquiv k ψ z = Bialgebra.TensorProduct.map (BialgHom.id k k) (ψ : X →ₐc[R] Y) z := rfl

end BaseChangeFunctoriality
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit"
end BC
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit"

end S42GAM
p2m_reactivate "P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM.Kit P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient.S42GAM"

open S42GAM in
set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {h : ℕ} (𝒢 : PDivisibleGroup O p h)
    (φ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v) (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[O] 𝒢.level v)
    (hφt : ∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v))
    (hDpt : ∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[O] 𝒢.level (v + 1)) =
      (Dp v : 𝒢.level v →ₐc[O] 𝒢.level v).comp (𝒢.transition v))

    {hT : ℕ} (T : ℕ → Type) [∀ v, CommRing (T v)] [∀ v, HopfAlgebra (ZMod p) (T v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (T v)] [∀ v, Module.Finite (ZMod p) (T v)]
    [∀ v, Module.Free (ZMod p) (T v)]
    (tT : ∀ v, T (v + 1) →ₐc[ZMod p] T v) (htT : ∀ v, Function.Surjective (tT v))
    (hrankT : ∀ v, Module.finrank (ZMod p) (T v) = p ^ (v * hT))
    (hkerT : ∀ v, RingHom.ker (tT v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (T (v + 1)) (p ^ v))
    (πT : ∀ v : ℕ, ZMod p ⊗[O] 𝒢.level v →ₐc[ZMod p] T v) (hπT : ∀ v, Function.Surjective (πT v))
    (hπTt : ∀ v : ℕ, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (tT v).comp (πT (v + 1)))
    (VerT : ∀ v : ℕ, T v ≃ₐc[ZMod p] T v)
    (hVerT : ∀ (v : ℕ) (ψ : CartierDual (ZMod p) (T v)), CartierDual.map (VerT v : T v →ₐc[ZMod p] T v) ψ = ψ ^ p)

    {hB : ℕ} (Bq : ℕ → Type) [∀ v, CommRing (Bq v)] [∀ v, HopfAlgebra (ZMod p) (Bq v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Bq v)] [∀ v, Module.Finite (ZMod p) (Bq v)]
    [∀ v, Module.Free (ZMod p) (Bq v)]
    (tB : ∀ v, Bq (v + 1) →ₐc[ZMod p] Bq v) (htB : ∀ v, Function.Surjective (tB v))
    (hrankBq : ∀ v, Module.finrank (ZMod p) (Bq v) = p ^ (v * hB))
    (hkerBq : ∀ v, RingHom.ker (tB v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Bq (v + 1)) (p ^ v))
    (jB : ∀ v : ℕ, Bq v →ₐc[ZMod p] ZMod p ⊗[O] 𝒢.level v) (hjB : ∀ v, Function.Injective (jB v))
    (hjBt : ∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)).comp (jB (v + 1)) = (jB v).comp (tB v))
    (hexT : ∀ v : ℕ, RingHom.ker (πT v : ZMod p ⊗[O] 𝒢.level v →ₐ[ZMod p] T v) =
      Ideal.map (jB v : Bq v →ₐ[ZMod p] ZMod p ⊗[O] 𝒢.level v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Bq v))))

    (hπTφ : ∀ v : ℕ, ∃ uT : T v →ₐc[ZMod p] T v, (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ v)) = uT.comp (πT v))
    (hπTD : ∀ v : ℕ, ∃ eT : T v →ₐc[ZMod p] T v,
      (πT v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp v : 𝒢.level v →ₐc[O] 𝒢.level v)) = eT.comp (πT v))
    (φB : ∀ v : ℕ, Bq v →ₐc[ZMod p] Bq v) (DB : ∀ v : ℕ, Bq v ≃ₐc[ZMod p] Bq v)
    (hjBφ : ∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ v)).comp (jB v) = (jB v).comp (φB v))
    (hjBD : ∀ v : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p))
        (Dp v : 𝒢.level v →ₐc[O] 𝒢.level v)).comp (jB v) = (jB v).comp (DB v : Bq v →ₐc[ZMod p] Bq v))

    {h₁ : ℕ} (G₁ : ℕ → Type) [∀ v, CommRing (G₁ v)] [∀ v, HopfAlgebra (ZMod p) (G₁ v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G₁ v)] [∀ v, Module.Finite (ZMod p) (G₁ v)]
    [∀ v, Module.Free (ZMod p) (G₁ v)]
    (t₁ : ∀ v, G₁ (v + 1) →ₐc[ZMod p] G₁ v) (ht₁ : ∀ v, Function.Surjective (t₁ v))
    (hrankG₁ : ∀ v, Module.finrank (ZMod p) (G₁ v) = p ^ (v * h₁))
    (hkerG₁ : ∀ v, RingHom.ker (t₁ v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G₁ (v + 1)) (p ^ v))
    (π₁ : ∀ v : ℕ, Bq v →ₐc[ZMod p] G₁ v) (hπ₁ : ∀ v, Function.Surjective (π₁ v))
    (hπ₁t : ∀ v : ℕ, (π₁ v).comp (tB v) = (t₁ v).comp (π₁ (v + 1)))

    {h₂ : ℕ} (G₂ : ℕ → Type) [∀ v, CommRing (G₂ v)] [∀ v, HopfAlgebra (ZMod p) (G₂ v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G₂ v)] [∀ v, Module.Finite (ZMod p) (G₂ v)]
    [∀ v, Module.Free (ZMod p) (G₂ v)]
    (t₂ : ∀ v, G₂ (v + 1) →ₐc[ZMod p] G₂ v) (ht₂ : ∀ v, Function.Surjective (t₂ v))
    (hrankG₂ : ∀ v, Module.finrank (ZMod p) (G₂ v) = p ^ (v * h₂))
    (hkerG₂ : ∀ v, RingHom.ker (t₂ v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G₂ (v + 1)) (p ^ v))
    (j₂ : ∀ v : ℕ, G₂ v →ₐc[ZMod p] Bq v) (hj₂ : ∀ v, Function.Injective (j₂ v))
    (hj₂t : ∀ v : ℕ, (tB v).comp (j₂ (v + 1)) = (j₂ v).comp (t₂ v))
    (hex : ∀ v : ℕ, RingHom.ker (π₁ v : Bq v →ₐ[ZMod p] G₁ v) =
      Ideal.map (j₂ v : G₂ v →ₐ[ZMod p] Bq v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (G₂ v))))

    (φ₁ : ∀ v : ℕ, G₁ v →ₐc[ZMod p] G₁ v) (φ₂ : ∀ v : ℕ, G₂ v →ₐc[ZMod p] G₂ v) (d₂ : ∀ v : ℕ, G₂ v ≃ₐc[ZMod p] G₂ v)
    (hπφ : ∀ v : ℕ, (π₁ v).comp (φB v) = (φ₁ v).comp (π₁ v))
    (hjφ : ∀ v : ℕ, (φB v).comp (j₂ v) = (j₂ v).comp (φ₂ v))
    (hjD : ∀ v : ℕ, (DB v : Bq v →ₐc[ZMod p] Bq v).comp (j₂ v) = (j₂ v).comp (d₂ v : G₂ v →ₐc[ZMod p] G₂ v))

    (Ver₁ : ∀ v : ℕ, G₁ v →ₐc[ZMod p] G₁ v)
    (hVer₁ : ∀ (v : ℕ) (ψ : CartierDual (ZMod p) (G₁ v)), CartierDual.map (Ver₁ v) ψ = ψ ^ p)

    (hE1 : ∀ v : ℕ, φ₁ v = Ver₁ v)

    (hE2 : ∀ (v : ℕ) (x : G₂ v), φ₂ v x = (d₂ v) (x ^ p)) :
    (∀ Fk : ZMod p ⊗[O] 𝒢.level 1 →ₐc[ZMod p] ZMod p ⊗[O] 𝒢.level 1, (∀ x, Fk x = x ^ p) →
          ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₐ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1), (∀ ψ, FD ψ = ψ ^ p) →
          ∃ (n : ℕ) (a b : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₐc[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)),
            (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ 1)) :
                CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                  CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)) ^ n =
              (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)) ∘ₗ
                  (a : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1))) *
                WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)) ∘ₗ
                  (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) →ₗ[ZMod p]
                    CartierDual (ZMod p) (ZMod p ⊗[O] 𝒢.level 1)))).ofConv) := by
  intro Fk hFk FD hFD
  haveI : Module.Free (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) := inferInstance
  haveI : Module.Finite (ZMod p) (ZMod p ⊗[O] 𝒢.level 1) := inferInstance
  let dd : ZMod p ⊗[O] 𝒢.level 1 ≃ₐc[ZMod p] ZMod p ⊗[O] 𝒢.level 1 := BC.baseChangeEquiv (ZMod p) (Dp 1)
  have hdd : (dd : ZMod p ⊗[O] 𝒢.level 1 →ₐc[ZMod p] ZMod p ⊗[O] 𝒢.level 1) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (Dp 1 : 𝒢.level 1 →ₐc[O] 𝒢.level 1) :=
    BC.baseChangeEquiv_toBialgHom (ZMod p) (Dp 1)
  obtain ⟨a, b, hab⟩ := coreG p (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (φ 1)) dd
    (πT 1) (hπT 1) (VerT 1) (hVerT 1) (jB 1) (hexT 1) (φB 1) (DB 1) (hjBφ 1) (by rw [hdd]; exact hjBD 1)
    (π₁ 1) (hπ₁ 1) (j₂ 1) (hex 1) (φ₁ 1) (φ₂ 1) (d₂ 1) (hπφ 1) (hjφ 1) (hjD 1) (Ver₁ 1) (hVer₁ 1) (hE1 1) (hE2 1)
    Fk hFk FD hFD
  exact ⟨2, a, b, hab⟩

end S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient
end P2MW
export P2MW.S_PDivisibleGroup_cartierDualMap_pow_eq_frobenius_conv_verschiebung_of_multiplicative_sub_of_verschiebung_sub_frobenius_quotient (solution)
