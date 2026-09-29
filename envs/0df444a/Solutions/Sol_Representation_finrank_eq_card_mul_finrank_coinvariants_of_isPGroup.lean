-- Prove2me | solution 1 for Representation.finrank_eq_card_mul_finrank_coinvariants_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d441ee3e-bd53-5d3c-8944-4efbec8a7034

import Mathlib
import Theorems.Thm_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace TateRankSol

open Representation

section CharP

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module k V]
  (τ : Representation k G V)

def regRep (d : ℕ) : Representation k G (Fin d → G → k) where
  toFun h :=
    { toFun := fun f i g => f i (h⁻¹ * g)
      map_add' := fun f₁ f₂ => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    refine LinearMap.ext fun f => ?_
    funext i g
    simp
  map_mul' h₁ h₂ := by
    refine LinearMap.ext fun f => ?_
    funext i g
    simp [mul_assoc]

@[scoped simp] theorem regRep_apply (d : ℕ) (h : G) (f : Fin d → G → k) (i : Fin d) (g : G) :
    regRep (k := k) d h f i g = f i (h⁻¹ * g) := rfl

def Phi {d : ℕ} (v : Fin d → V) : (Fin d → G → k) →ₗ[k] V where
  toFun f := ∑ i, ∑ g, f i g • τ g (v i)
  map_add' f₁ f₂ := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem Phi_apply {d : ℕ} (v : Fin d → V) (f : Fin d → G → k) :
    Phi τ v f = ∑ i, ∑ g, f i g • τ g (v i) := rfl

theorem Phi_regRep {d : ℕ} (v : Fin d → V) (h : G) (f : Fin d → G → k) :
    Phi τ v (regRep d h f) = τ h (Phi τ v f) := by
  rw [Phi_apply, Phi_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]

  rw [← (Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun g => rfl))]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [regRep_apply, inv_mul_cancel_left, map_smul, map_mul, Module.End.mul_apply]

def delta [DecidableEq G] {d : ℕ} (i : Fin d) : Fin d → G → k :=
  fun i' g => if i' = i ∧ g = 1 then 1 else 0

theorem Phi_delta [DecidableEq G] {d : ℕ} (v : Fin d → V) (i : Fin d) : Phi τ v (delta i) = v i := by
  rw [Phi_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single 1]
    · simp [delta]
    · intro g _ hg
      simp [delta, hg]
    · intro h1; exact absurd (Finset.mem_univ _) h1
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro g _
    simp [delta, hi']
  · intro hi; exact absurd (Finset.mem_univ _) hi

theorem apply_eq_apply_one_of_fixed {d : ℕ} (w : Fin d → G → k)
    (hw : ∀ h : G, regRep d h w = w) (i : Fin d) (g : G) : w i g = w i 1 := by
  have := congrFun (congrFun (hw g) i) g
  rw [regRep_apply, inv_mul_cancel] at this
  exact this.symm

theorem Phi_const {d : ℕ} (v : Fin d → V) (c : Fin d → k) :
    Phi τ v (fun i _ => c i) = τ.norm (∑ i, c i • v i) := by
  rw [Phi_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Representation.norm, LinearMap.sum_apply, Finset.smul_sum]

variable [FiniteDimensional k V]

theorem finrank_eq_card_mul_of_ker_norm_le (hG : IsPGroup p G)
    (hker : ∀ v, τ.norm v = 0 → v ∈ Coinvariants.ker τ) :
    Module.finrank k V = Fintype.card G * Module.finrank k (Coinvariants τ) := by
  classical
  set d := Module.finrank k (Coinvariants τ) with hd
  let b : Module.Basis (Fin d) k (Coinvariants τ) := Module.finBasis k (Coinvariants τ)

  have hlift : ∀ i, ∃ v : V, Coinvariants.mk τ v = b i := fun i => Coinvariants.mk_surjective τ (b i)
  choose v hv using hlift
  set Φ := Phi τ v with hΦ

  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    obtain ⟨f, hfK, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne

    let Ksub : Subrepresentation (regRep (k := k) (G := G) d) :=
      { toSubmodule := LinearMap.ker Φ
        apply_mem_toSubmodule := fun h x hx => by
          rw [LinearMap.mem_ker] at hx ⊢
          rw [hΦ, Phi_regRep, ← hΦ, hx, map_zero] }
    have hf0' : (⟨f, hfK⟩ : ↥Ksub.toSubmodule) ≠ 0 := fun h0 => hf0 (congrArg Subtype.val h0)
    obtain ⟨w, hw0, hw⟩ := Representation.exists_ne_zero_forall_apply_eq_of_isPGroup hG
      Ksub.toRepresentation hf0'
    have hwfix : ∀ h : G, regRep d h (w : Fin d → G → k) = w := fun h =>
      congrArg Subtype.val (hw h)
    set c : Fin d → k := fun i => (w : Fin d → G → k) i 1 with hc
    have hwc : (w : Fin d → G → k) = fun i _ => c i := by
      funext i g
      exact apply_eq_apply_one_of_fixed _ hwfix i g
    have hN : τ.norm (∑ i, c i • v i) = 0 := by
      rw [← Phi_const, ← hwc]
      exact w.2
    have hmk : Coinvariants.mk τ (∑ i, c i • v i) = 0 :=
      (Coinvariants.mk_eq_zero τ).mpr (hker _ hN)
    rw [map_sum] at hmk
    simp only [map_smul, hv] at hmk
    have hc0 : ∀ i, c i = 0 := fun i => by
      have := Fintype.linearIndependent_iff.mp b.linearIndependent c hmk i
      exact this
    apply hw0
    apply Subtype.ext
    rw [hwc]
    funext i g
    simp [hc0 i]

  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    set U := LinearMap.range Φ with hU
    have hlt : U < ⊤ := lt_top_iff_ne_top.mpr hne

    have hUstab : ∀ (h : G) (u : V), u ∈ U → τ h u ∈ U := by
      rintro h _ ⟨f, rfl⟩
      exact ⟨regRep d h f, Phi_regRep τ v h f⟩
    have hdec : ∀ x : V, ∃ u ∈ U, x - u ∈ Coinvariants.ker τ := by
      intro x
      refine ⟨∑ i, b.repr (Coinvariants.mk τ x) i • v i, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        exact ⟨delta i, Phi_delta τ v i⟩
      · rw [← Coinvariants.mk_eq_zero, map_sub, map_sum]
        simp only [map_smul, hv]
        rw [b.sum_repr, sub_self]

    obtain ⟨f, hf0, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hfU' : ∀ u ∈ U, f u = 0 := by
      intro u hu
      have : f u ∈ U.map f := Submodule.mem_map_of_mem hu
      rwa [hfU, Submodule.mem_bot] at this

    let Ann : Subrepresentation (Representation.dual τ) :=
      { toSubmodule := U.dualAnnihilator
        apply_mem_toSubmodule := fun h φ hφ => by
          rw [Submodule.mem_dualAnnihilator] at hφ ⊢
          intro u hu
          rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
          exact hφ _ (hUstab _ _ hu) }
    have hfA : f ∈ Ann.toSubmodule := (Submodule.mem_dualAnnihilator f).mpr hfU'
    obtain ⟨φ, hφ0, hφ⟩ := Representation.exists_ne_zero_forall_apply_eq_of_isPGroup
      (V := ↥Ann.toSubmodule) hG Ann.toRepresentation (v := ⟨f, hfA⟩)
      (fun h0 => hf0 (congrArg Subtype.val h0))
    have hφfix : ∀ (h : G) (x : V), (φ : Module.Dual k V) (τ h x) = (φ : Module.Dual k V) x := by
      intro h x
      have h1 : ((Ann.toRepresentation h⁻¹ φ : ↥Ann.toSubmodule) : Module.Dual k V) =
          (φ : Module.Dual k V) ∘ₗ τ h := by
        show ((Representation.dual τ h⁻¹).restrict (Ann.apply_mem_toSubmodule h⁻¹) φ :
          Module.Dual k V) = _
        rw [LinearMap.restrict_apply]
        show Representation.dual τ h⁻¹ (φ : Module.Dual k V) = _
        rw [Representation.dual_apply, Module.Dual.transpose_apply, inv_inv]
      have := congrArg Subtype.val (hφ h⁻¹)
      rw [h1] at this
      exact DFunLike.congr_fun this x
    have hφI : ∀ x ∈ Coinvariants.ker τ, (φ : Module.Dual k V) x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨g, z⟩, rfl⟩ := hy
        simp only [map_sub, hφfix, sub_self]
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    have hφU : ∀ u ∈ U, (φ : Module.Dual k V) u = 0 := (Submodule.mem_dualAnnihilator _).mp φ.2
    apply hφ0
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, hu, hxu⟩ := hdec x
    have : x = u + (x - u) := by abel
    rw [this]
    show (φ : Module.Dual k V) (u + (x - u)) = 0
    rw [map_add, hφU u hu, hφI _ hxu, add_zero]

  have e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Module.finrank_pi, smul_eq_mul, mul_comm]

end CharP

section Reduction

p2m_open "TensorProduct Representation.TensorProduct"

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsLocalRing 𝒪]
  {G : Type} [Group G] [Fintype G]
  {P : Type} [AddCommGroup P] [Module 𝒪 P]
  (ρ : Representation 𝒪 G P)

local notation "kk" => IsLocalRing.ResidueField 𝒪
local notation "VV" => TensorProduct 𝒪 (IsLocalRing.ResidueField 𝒪) P

def rhoV : Representation kk G VV :=
  (Module.End.baseChangeHom 𝒪 kk P).toMonoidHom.comp ρ

theorem rhoV_apply (g : G) : rhoV ρ g = (ρ g).baseChange kk := rfl

theorem rhoV_tmul (g : G) (c : kk) (x : P) : rhoV ρ g (c ⊗ₜ x) = c ⊗ₜ ρ g x := by
  rw [rhoV_apply, LinearMap.baseChange_tmul]

def mkV : P →ₗ[𝒪] VV := TensorProduct.mk 𝒪 kk P 1

theorem mkV_apply (x : P) : mkV x = (1 : kk) ⊗ₜ x := rfl

theorem tmul_eq_smul_mkV (c : kk) (x : P) : c ⊗ₜ[𝒪] x = c • mkV x := by
  rw [mkV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem mkV_surjective : Function.Surjective (mkV (𝒪 := 𝒪) (P := P)) := by
  intro v
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c x =>
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨r • x, ?_⟩
    rw [mkV_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

theorem rhoV_mkV (g : G) (x : P) : rhoV ρ g (mkV x) = mkV (ρ g x) := rhoV_tmul ρ g 1 x

theorem norm_mkV (x : P) : (rhoV ρ).norm (mkV x) = mkV (ρ.norm x) := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => rhoV_mkV ρ g x

theorem mem_smul_top_of_mkV_eq_zero (x : P) (hx : mkV (𝒪 := 𝒪) x = 0) :
    x ∈ (IsLocalRing.maximalIdeal 𝒪 • ⊤ : Submodule 𝒪 P) := by
  have h := TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (M := P) (IsLocalRing.maximalIdeal 𝒪) x
  have hx' : ((1 : kk) ⊗ₜ[𝒪] x : VV) = 0 := hx
  have : (TensorProduct.quotTensorEquivQuotSMul P (IsLocalRing.maximalIdeal 𝒪))
      ((1 : 𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪) ⊗ₜ[𝒪] x) = 0 := by
    have e0 : ((1 : 𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪) ⊗ₜ[𝒪] x) = 0 := hx'
    rw [e0, map_zero]
  rw [h] at this
  exact (Submodule.Quotient.mk_eq_zero _).mp this

theorem mkV_mem_ker_of_mem (x : P) (hx : x ∈ Coinvariants.ker ρ) :
    mkV x ∈ Coinvariants.ker (rhoV ρ) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g, z⟩, rfl⟩ := hy
    have : mkV (𝒪 := 𝒪) (ρ g z - z) = rhoV ρ g (mkV z) - mkV z := by rw [map_sub, rhoV_mkV]
    rw [this]
    exact Coinvariants.sub_mem_ker _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul, ← algebraMap_smul (IsLocalRing.ResidueField 𝒪) c (mkV x)]
    exact Submodule.smul_mem _ _ hx

variable [Module.IsTorsionFree 𝒪 P]

theorem ker_normV_le
    (h0 : ∀ w : P, (∀ g : G, ρ g w = w) → ∃ m : P, ρ.norm m = w)
    (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Coinvariants.ker ρ)
    (v : VV) (hv : (rhoV ρ).norm v = 0) : v ∈ Coinvariants.ker (rhoV ρ) := by
  obtain ⟨x, rfl⟩ := mkV_surjective v
  rw [norm_mkV] at hv
  have hNx := mem_smul_top_of_mkV_eq_zero _ hv

  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal 𝒪)).principal
  rw [hϖ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hNx
  obtain ⟨w, -, hw⟩ := hNx

  by_cases hϖ0 : ϖ = 0
  · rw [hϖ0, zero_smul] at hw
    exact mkV_mem_ker_of_mem ρ x (h1 x hw.symm)

  have hwinv : ∀ g : G, ρ g w = w := by
    intro g
    have h2 : ϖ • (ρ g w - w) = 0 := by
      rw [smul_sub, ← map_smul, hw, Representation.self_norm_apply, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_right hϖ0).mp h2)
  obtain ⟨m, hm⟩ := h0 w hwinv
  have hN : ρ.norm (x - ϖ • m) = 0 := by
    rw [map_sub, map_smul, hm, hw, sub_self]
  have hmem := h1 _ hN
  have hx : x = (x - ϖ • m) + ϖ • m := by abel
  rw [hx, map_add]
  refine Submodule.add_mem _ (mkV_mem_ker_of_mem ρ _ hmem) ?_
  have : mkV (𝒪 := 𝒪) (ϖ • m) = 0 := by
    rw [map_smul, ← algebraMap_smul (IsLocalRing.ResidueField 𝒪) ϖ (mkV m)]
    have hres : algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪) ϖ = 0 := by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, hϖ]
      exact Ideal.mem_span_singleton_self ϖ
    rw [hres, zero_smul]
  rw [this]
  exact Submodule.zero_mem _

theorem isTorsionFree_coinvariants (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Coinvariants.ker ρ) :
    Module.IsTorsionFree 𝒪 (Coinvariants ρ) := by

  have hker : Coinvariants.ker ρ = LinearMap.ker ρ.norm := by
    apply le_antisymm
    · rw [Coinvariants.ker, Submodule.span_le]
      rintro _ ⟨⟨g, z⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Representation.norm_self_apply, sub_self]
    · intro v hv
      exact h1 v hv
  let e : Coinvariants ρ ≃ₗ[𝒪] ↥(LinearMap.range ρ.norm) :=
    (Submodule.quotEquivOfEq _ _ hker).trans ρ.norm.quotKerEquivRange
  have hinj : Function.Injective (fun m : Coinvariants ρ => ((e m : ↥(LinearMap.range ρ.norm)) : P)) :=
    Subtype.val_injective.comp e.injective
  exact hinj.moduleIsTorsionFree _ (fun c m => by simp only [map_smul, Submodule.coe_smul])

theorem finrank_coinvariants_rhoV [Module.Finite 𝒪 P]
    (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Coinvariants.ker ρ) :
    Module.finrank kk (Coinvariants (rhoV ρ)) = Module.finrank 𝒪 (Coinvariants ρ) := by
  haveI := isTorsionFree_coinvariants ρ h1
  haveI : Module.Free 𝒪 (Coinvariants ρ) := Module.free_of_finite_type_torsion_free'

  set q : P →ₗ[𝒪] Coinvariants ρ := Coinvariants.mk ρ with hq
  set qk : VV →ₗ[kk] kk ⊗[𝒪] Coinvariants ρ := q.baseChange kk with hqk
  have hqsurj : Function.Surjective qk := by
    intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective kk (Coinvariants.mk_surjective ρ) y
    refine ⟨x, ?_⟩
    rw [← hx, hqk]
    exact congrFun (LinearMap.baseChange_eq_ltensor q) x
  have hkerq : LinearMap.ker qk = Coinvariants.ker (rhoV ρ) := by
    apply le_antisymm
    · intro v hv
      have hv' : v ∈ LinearMap.ker (q.lTensor kk) := by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [← hv]
        exact (congrFun (LinearMap.baseChange_eq_ltensor q) v).symm
      have hle : LinearMap.ker (q.lTensor kk) =
          LinearMap.range ((Coinvariants.ker ρ).subtype.lTensor kk) := lTensor_mkQ kk _
      rw [hle] at hv'
      obtain ⟨t, rfl⟩ := hv'
      clear hv
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul c y =>
        rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, tmul_eq_smul_mkV]
        exact Submodule.smul_mem _ _ (mkV_mem_ker_of_mem ρ _ y.2)
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · rw [Coinvariants.ker, Submodule.span_le]
      rintro _ ⟨⟨g, z⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      obtain ⟨x, rfl⟩ := mkV_surjective z
      rw [rhoV_mkV, mkV_apply, mkV_apply, hqk, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        hq, Coinvariants.mk_self_apply]
  have e : Coinvariants (rhoV ρ) ≃ₗ[kk] kk ⊗[𝒪] Coinvariants ρ :=
    (Submodule.quotEquivOfEq _ _ hkerq.symm).trans (qk.quotKerEquivOfSurjective hqsurj)
  rw [e.finrank_eq, Module.finrank_baseChange]

theorem main (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    (hG : IsPGroup p G) [Module.Finite 𝒪 P]
    (h0 : ∀ w : P, (∀ g : G, ρ g w = w) → ∃ m : P, ρ.norm m = w)
    (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Coinvariants.ker ρ) :
    Module.finrank 𝒪 P = Fintype.card G * Module.finrank 𝒪 (Coinvariants ρ) := by
  haveI : Module.Free 𝒪 P := Module.free_of_finite_type_torsion_free'
  have hV : Module.finrank kk VV = Module.finrank 𝒪 P := Module.finrank_baseChange
  rw [← hV, ← finrank_coinvariants_rhoV ρ h1]
  exact finrank_eq_card_mul_of_ker_norm_le (rhoV ρ) hG (ker_normV_le ρ h0 h1)

end Reduction

end TateRankSol
p2m_reactivate "P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup.TateRankSol"

end
p2m_reactivate "P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup.TateRankSol"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField 𝒪) p]
    {G : Type} [Group G] [Fintype G] (hG : IsPGroup p G)
    {P : Type} [AddCommGroup P] [Module 𝒪 P] [Module.Finite 𝒪 P] [Module.IsTorsionFree 𝒪 P]
    (ρ : Representation 𝒪 G P)
    (h0 : ∀ w : P, (∀ g : G, ρ g w = w) → ∃ m : P, ρ.norm m = w)
    (h1 : ∀ v : P, ρ.norm v = 0 → v ∈ Representation.Coinvariants.ker ρ) :
    Module.finrank 𝒪 P = Fintype.card G * Module.finrank 𝒪 (Representation.Coinvariants ρ) :=
  TateRankSol.main ρ p hG h0 h1

end S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup
end P2MW
export P2MW.S_Representation_finrank_eq_card_mul_finrank_coinvariants_of_isPGroup (solution)
