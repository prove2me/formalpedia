-- Prove2me | solution 1 for Submodule.exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/86f13dbe-31b1-5ce5-be5c-782bf3a8949b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Module

namespace PerfPairDuality

section RWorld

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]

def perp (B : V →ₗ[R] V →ₗ[R] R) (W : Submodule R V) : Submodule R V where
  carrier := {v | ∀ w ∈ W, B v w = 0}
  add_mem' {v v'} hv hv' w hw := by rw [map_add, LinearMap.add_apply, hv w hw, hv' w hw, add_zero]
  zero_mem' w hw := by rw [map_zero, LinearMap.zero_apply]
  smul_mem' c v hv w hw := by rw [map_smul, LinearMap.smul_apply, hv w hw, smul_zero]

theorem mem_perp {B : V →ₗ[R] V →ₗ[R] R} {W : Submodule R V} {v : V} :
    v ∈ perp B W ↔ ∀ w ∈ W, B v w = 0 := Iff.rfl

theorem le_perp_perp {B : V →ₗ[R] V →ₗ[R] R} (hanti : ∀ v w, B v w = - B w v) (W : Submodule R V) :
    W ≤ perp B (perp B W) := by
  intro v hv y hy
  rw [hanti, hy v hv, neg_zero]

theorem summand_of_free_quotient [IsLocalRing R] (W : Submodule R V)
    (hfree : Module.Free R (V ⧸ W)) (hfin : Module.Finite R (V ⧸ W)) :
    Module.Free R W ∧ Module.Finite R W ∧
      finrank R W + finrank R (V ⧸ W) = finrank R V ∧
      ∀ φ : W →ₗ[R] R, ∃ ψ : V →ₗ[R] R, ψ.comp W.subtype = φ := by
  haveI := hfree
  haveI := hfin

  obtain ⟨s, hs⟩ := Module.projective_lifting_property W.mkQ (LinearMap.id : (V ⧸ W) →ₗ[R] (V ⧸ W))
    (Submodule.mkQ_surjective W)

  have hmem : ∀ v : V, v - s (W.mkQ v) ∈ W := fun v => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun hs (W.mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ρ : V →ₗ[R] W := LinearMap.codRestrict W (LinearMap.id - s.comp W.mkQ) fun v => hmem v
  have hρ : ρ.comp W.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    show (w : V) - s (W.mkQ (w : V)) = w
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr w.2, map_zero, sub_zero]
  have hρsurj : Function.Surjective ρ := fun w => ⟨(w : V), LinearMap.congr_fun hρ w⟩
  haveI hWproj : Module.Projective R W := Module.Projective.of_split W.subtype ρ hρ
  haveI hWfin : Module.Finite R W := Module.Finite.of_surjective ρ hρsurj
  haveI hWfree : Module.Free R W := Module.free_of_flat_of_isLocalRing

  let e : V ≃ₗ[R] (W × (V ⧸ W)) :=
    { toFun := fun v => (ρ v, W.mkQ v)
      invFun := fun p => (p.1 : V) + s p.2
      map_add' := fun v v' => by simp only [map_add, Prod.mk_add_mk]
      map_smul' := fun c v => by simp only [map_smul, RingHom.id_apply, Prod.smul_mk]
      left_inv := fun v => by
        show ((v - s (W.mkQ v) : V)) + s (W.mkQ v) = v
        abel
      right_inv := fun p => by
        obtain ⟨w, q⟩ := p
        have h1 : W.mkQ ((w : V) + s q) = q := by
          rw [map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr w.2, zero_add]
          have := LinearMap.congr_fun hs q
          rwa [LinearMap.comp_apply, LinearMap.id_apply] at this
        have h2 : ρ ((w : V) + s q) = w := by
          apply Subtype.ext
          show ((w : V) + s q) - s (W.mkQ ((w : V) + s q)) = w
          rw [h1, add_sub_cancel_right]
        exact Prod.ext h2 h1 }
  refine ⟨hWfree, hWfin, ?_, fun φ => ⟨φ.comp ρ, by rw [LinearMap.comp_assoc, hρ, LinearMap.comp_id]⟩⟩
  rw [← Module.finrank_prod, ← e.finrank_eq]

theorem free_quotient_perp [IsLocalRing R] {B : V →ₗ[R] V →ₗ[R] R} (hB : Function.Bijective B)
    (W : Submodule R V)
    (hfree : Module.Free R (V ⧸ W)) (hfin : Module.Finite R (V ⧸ W)) :
    Module.Free R (V ⧸ perp B W) ∧ Module.Finite R (V ⧸ perp B W) ∧
      finrank R (V ⧸ perp B W) + finrank R (V ⧸ W) = finrank R V := by
  obtain ⟨hWfree, hWfin, hrank, hext⟩ := summand_of_free_quotient W hfree hfin
  haveI := hWfree
  haveI := hWfin

  let lam : V →ₗ[R] (W →ₗ[R] R) := (LinearMap.lcomp R R W.subtype).comp B
  have hlam : ∀ v w, lam v w = B v (w : V) := fun v w => rfl
  have hker : LinearMap.ker lam = perp B W := by
    ext v
    rw [LinearMap.mem_ker, mem_perp]
    constructor
    · intro h w hw
      have := LinearMap.congr_fun h ⟨w, hw⟩
      rwa [hlam, LinearMap.zero_apply] at this
    · intro h
      apply LinearMap.ext
      intro w
      rw [hlam, LinearMap.zero_apply]
      exact h w w.2
  have hsurj : Function.Surjective lam := by
    intro φ
    obtain ⟨ψ, hψ⟩ := hext φ
    obtain ⟨v, hv⟩ := hB.2 ψ
    refine ⟨v, LinearMap.ext fun w => ?_⟩
    rw [hlam, hv, ← hψ, LinearMap.comp_apply, Submodule.subtype_apply]
  let e : (V ⧸ perp B W) ≃ₗ[R] (W →ₗ[R] R) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (lam.quotKerEquivOfSurjective hsurj)
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_linearMap_self, hrank]

theorem eq_of_le_of_free_quotient [Nontrivial R] {W₁ W₂ : Submodule R V} (hle : W₁ ≤ W₂)
    (h₁ : Module.Free R (V ⧸ W₁)) (h₁' : Module.Finite R (V ⧸ W₁))
    (h₂ : Module.Free R (V ⧸ W₂)) (h₂' : Module.Finite R (V ⧸ W₂))
    (hrank : finrank R (V ⧸ W₁) = finrank R (V ⧸ W₂)) : W₁ = W₂ := by
  haveI := h₁; haveI := h₁'; haveI := h₂; haveI := h₂'
  refine le_antisymm hle ?_

  let q : (V ⧸ W₁) →ₗ[R] (V ⧸ W₂) := Submodule.factor hle
  let e : (V ⧸ W₂) ≃ₗ[R] (V ⧸ W₁) := LinearEquiv.ofFinrankEq _ _ hrank.symm
  have hq : Function.Surjective q := Submodule.factor_surjective hle
  have hinj : Function.Injective (e.toLinearMap.comp q) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hq)
  intro w hw
  have h0 : (e.toLinearMap.comp q) (Submodule.Quotient.mk w) = 0 := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
    show Submodule.factor hle (Submodule.mkQ W₁ w) = 0
    rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hw
  rw [← (Submodule.Quotient.mk_eq_zero W₁)]
  exact hinj (h0.trans (map_zero _).symm)

end RWorld

section OWorld

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
  {A : Type*} [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
  {P : Type*} [AddCommGroup P] [Module A P] [Module 𝒪 P] [IsScalarTower 𝒪 A P]
  [Module.Finite 𝒪 P] [Module.Free 𝒪 P]
  [DecidableEq (Module.Free.ChooseBasisIndex 𝒪 P)] [DecidableEq (Module.Free.ChooseBasisIndex 𝒪 A)]
  (r : 𝒪)

set_option quotPrecheck false in
local notation "Rr" => 𝒪 ⧸ Ideal.span (Singleton.singleton r)
set_option quotPrecheck false in
local notation "π₀" => Ideal.Quotient.mk (Ideal.span (Singleton.singleton r))
local notation "κ" => Module.Free.ChooseBasisIndex 𝒪 P
local notation "ι" => Module.Free.ChooseBasisIndex 𝒪 A
local notation "bP" => Module.Free.chooseBasis 𝒪 P
local notation "bA" => Module.Free.chooseBasis 𝒪 A

def piL : 𝒪 →ₗ[𝒪] Rr := (Ideal.Quotient.mkₐ 𝒪 (Ideal.span ({r} : Set 𝒪))).toLinearMap

@[scoped simp] theorem piL_apply (c : 𝒪) : piL r c = π₀ c := rfl

theorem base_smul_eq (c : 𝒪) (x : Rr) : c • x = π₀ c * x := rfl

def redP : P →ₗ[𝒪] (κ → Rr) := ((piL r).compLeft κ).comp (bP).equivFun.toLinearMap

theorem redP_apply (v : P) (i : κ) : redP (P := P) r v i = π₀ ((bP).repr v i) := rfl

theorem redP_basis (i : κ) : redP (P := P) r ((bP) i) = Pi.single i 1 := by
  ext j
  rw [redP_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

theorem redP_surjective : Function.Surjective (redP (P := P) r) := by
  intro u
  choose c hc using fun i => Ideal.Quotient.mk_surjective (u i)
  refine ⟨(bP).equivFun.symm c, ?_⟩
  ext i
  rw [redP_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hc]

theorem redP_eq_zero_iff (v : P) : redP r v = 0 ↔ ∃ w : P, v = r • w := by
  constructor
  · intro h
    have hi : ∀ i, ∃ c : 𝒪, c * r = (bP).repr v i := fun i => by
      have := congr_fun h i
      rw [redP_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at this
      exact this
    choose c hc using hi
    refine ⟨(bP).equivFun.symm c, ?_⟩
    apply (bP).equivFun.injective
    ext i
    rw [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_apply,
      ← hc, mul_comm]
  · rintro ⟨w, rfl⟩
    ext i
    rw [redP_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)

theorem redP_smul (c : 𝒪) (v : P) : redP r (c • v) = (π₀ c) • redP r v := by
  rw [map_smul]
  ext i
  rfl

def Ebar (E : Submodule A P) : Submodule Rr (κ → Rr) where
  carrier := redP r '' (E : Set P)
  zero_mem' := ⟨0, E.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, E.add_mem hv hw, map_add _ _ _⟩
  smul_mem' := by
    rintro c _ ⟨v, hv, rfl⟩
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨c' • v, E.smul_of_tower_mem c' hv, redP_smul r c' v⟩

theorem mem_Ebar_iff {E : Submodule A P} (hrE : ∀ w : P, r • w ∈ E) (v : P) :
    redP r v ∈ Ebar r E ↔ v ∈ E := by
  constructor
  · rintro ⟨v', hv', h⟩
    have h0 : redP r (v - v') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨w, hw⟩ := (redP_eq_zero_iff r _).mp h0
    have : v = v' + r • w := by rw [← hw]; abel
    rw [this]
    exact E.add_mem hv' (hrE w)
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem mem_Ebar_iff' {E : Submodule A P} (u : κ → Rr) : u ∈ Ebar r E ↔ ∃ v ∈ E, redP r v = u :=
  Iff.rfl

variable (β : P →ₗ[𝒪] P →ₗ[𝒪] 𝒪)

def Bbar : (κ → Rr) →ₗ[Rr] (κ → Rr) →ₗ[Rr] Rr :=
  (Pi.basisFun Rr κ).constr Rr fun i => (Pi.basisFun Rr κ).constr Rr fun j => π₀ (β ((bP) i) ((bP) j))

theorem Bbar_single (i j : κ) : Bbar r β (Pi.single i 1) (Pi.single j 1) = π₀ (β ((bP) i) ((bP) j)) := by
  rw [Bbar, ← Pi.basisFun_apply, ← Pi.basisFun_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]

theorem Bbar_redP (v w : P) : Bbar r β (redP r v) (redP r w) = π₀ (β v w) := by

  let L₁ : P →ₗ[𝒪] P →ₗ[𝒪] Rr := LinearMap.mk₂ 𝒪 (fun v w => Bbar r β (redP r v) (redP r w))
    (fun v v' w => by
      rw [map_add, map_add, LinearMap.add_apply])
    (fun c v w => by
      rw [redP_smul, map_smul, LinearMap.smul_apply, base_smul_eq, smul_eq_mul])
    (fun v w w' => by
      rw [map_add, map_add])
    (fun c v w => by
      rw [redP_smul, map_smul, base_smul_eq, smul_eq_mul])
  let L₂ : P →ₗ[𝒪] P →ₗ[𝒪] Rr := β.compr₂ (piL r)
  have h : L₁ = L₂ := by
    refine (bP).ext fun i => (bP).ext fun j => ?_
    show Bbar r β (redP r ((bP) i)) (redP r ((bP) j)) = π₀ (β ((bP) i) ((bP) j))
    rw [redP_basis, redP_basis, Bbar_single]
  have := congrArg (fun L : P →ₗ[𝒪] P →ₗ[𝒪] Rr => L v w) h
  exact this

theorem Bbar_antisymm (hanti : ∀ v w, β v w = - β w v) (u u' : κ → Rr) : Bbar r β u u' = - Bbar r β u' u := by
  obtain ⟨v, rfl⟩ := redP_surjective r u
  obtain ⟨v', rfl⟩ := redP_surjective r u'
  rw [Bbar_redP, Bbar_redP, hanti, map_neg]

theorem exists_eq_smul_of_forall_mem (hβ : Function.Bijective β) (v : P)
    (h : ∀ w, β v w ∈ Ideal.span ({r} : Set 𝒪)) : ∃ v' : P, v = r • v' := by
  have hi : ∀ i, ∃ c : 𝒪, c * r = β v ((bP) i) := fun i => Ideal.mem_span_singleton'.mp (h _)
  choose c hc using hi
  let f : P →ₗ[𝒪] 𝒪 := (bP).constr 𝒪 c
  have hf : r • f = β v := by
    refine (bP).ext fun i => ?_
    rw [LinearMap.smul_apply, Module.Basis.constr_basis, smul_eq_mul, mul_comm, hc]
  obtain ⟨v', hv'⟩ := hβ.2 f
  refine ⟨v', hβ.1 ?_⟩
  rw [map_smul, hv', hf]

theorem exists_repr_functional (hβ : Function.Bijective β) (g : P →ₗ[𝒪] Rr) :
    ∃ y : P, ∀ w, π₀ (β y w) = g w := by
  obtain ⟨χ, hχ⟩ := Module.projective_lifting_property (piL r) g Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := hβ.2 χ
  refine ⟨y, fun w => ?_⟩
  rw [hy, ← hχ, LinearMap.comp_apply, piL_apply]

theorem Bbar_bijective (hβ : Function.Bijective β) : Function.Bijective (Bbar (P := P) r β) := by
  constructor
  · intro u u' h
    obtain ⟨v, rfl⟩ := redP_surjective r u
    obtain ⟨v', rfl⟩ := redP_surjective r u'
    rw [← sub_eq_zero, ← map_sub, redP_eq_zero_iff]
    refine exists_eq_smul_of_forall_mem r β hβ _ fun w => ?_
    have hw := LinearMap.congr_fun h (redP r w)
    rw [Bbar_redP, Bbar_redP] at hw
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, LinearMap.sub_apply, map_sub, hw, sub_self]
  · intro ψ
    obtain ⟨y, hy⟩ := exists_repr_functional r β hβ ((ψ.restrictScalars 𝒪).comp (redP r))
    refine ⟨redP r y, LinearMap.ext fun u => ?_⟩
    obtain ⟨w, rfl⟩ := redP_surjective r u
    rw [Bbar_redP, hy]
    rfl

variable (Φ : P →ₗ[𝒪] (A →ₗ[𝒪] 𝒪 ⧸ Ideal.span ({r} : Set 𝒪)))

def coordA : (A →ₗ[𝒪] Rr) →ₗ[𝒪] (ι → Rr) := ((bA).constr 𝒪 (M' := Rr)).symm.toLinearMap

@[scoped simp] theorem coordA_apply (φ : A →ₗ[𝒪] Rr) (i : ι) : coordA (A := A) r φ i = φ ((bA) i) :=
  Module.Basis.constr_symm_apply _ _ φ i

theorem coordA_bijective : Function.Bijective (coordA (A := A) r) :=
  ((bA).constr 𝒪 (M' := Rr)).symm.bijective

def PhiP : P →ₗ[𝒪] (ι → Rr) := (coordA r).comp Φ

theorem PhiP_apply (v : P) (i : ι) : PhiP r Φ v i = Φ v ((bA) i) := coordA_apply r _ i

theorem PhiP_eq_zero_iff {E : Submodule A P} (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) (v : P) :
    PhiP r Φ v = 0 ↔ v ∈ E := by
  rw [← hΦk, PhiP, LinearMap.comp_apply]
  constructor
  · intro h
    exact (coordA_bijective (A := A) r).1 (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem PhiP_surjective (hΦs : Function.Surjective Φ) : Function.Surjective (PhiP r Φ) :=
  (coordA_bijective (A := A) r).2.comp hΦs

def Phibar : (κ → Rr) →ₗ[Rr] (ι → Rr) := (Pi.basisFun Rr κ).constr Rr fun j => PhiP r Φ ((bP) j)

theorem Phibar_redP (hrΦ : ∀ w : P, Φ (r • w) = 0) (v : P) : Phibar r Φ (redP r v) = PhiP r Φ v := by
  let L₁ : P →ₗ[𝒪] (ι → Rr) := ((Phibar r Φ).restrictScalars 𝒪).comp (redP r)
  have h : L₁ = PhiP r Φ := by
    refine (bP).ext fun j => ?_
    show Phibar r Φ (redP r ((bP) j)) = PhiP r Φ ((bP) j)
    rw [redP_basis, Phibar, ← Pi.basisFun_apply, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h v

theorem Phibar_surjective (hrΦ : ∀ w : P, Φ (r • w) = 0) (hΦs : Function.Surjective Φ) :
    Function.Surjective (Phibar (P := P) r Φ) := by
  intro u
  obtain ⟨v, hv⟩ := PhiP_surjective r Φ hΦs u
  exact ⟨redP r v, by rw [Phibar_redP r Φ hrΦ, hv]⟩

theorem ker_Phibar {E : Submodule A P} (hrE : ∀ w : P, r • w ∈ E) (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) :
    LinearMap.ker (Phibar r Φ) = Ebar r E := by
  have hrΦ : ∀ w : P, Φ (r • w) = 0 := fun w => (hΦk _).mpr (hrE w)
  ext u
  obtain ⟨v, rfl⟩ := redP_surjective r u
  rw [LinearMap.mem_ker, Phibar_redP r Φ hrΦ, PhiP_eq_zero_iff r Φ hΦk, mem_Ebar_iff r hrE]

theorem free_quotient_Ebar [Nontrivial (𝒪 ⧸ Ideal.span ({r} : Set 𝒪))] {E : Submodule A P}
    (hrE : ∀ w : P, r • w ∈ E) (hΦs : Function.Surjective Φ)
    (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) :
    Module.Free Rr ((κ → Rr) ⧸ Ebar r E) ∧ Module.Finite Rr ((κ → Rr) ⧸ Ebar r E) ∧
      finrank Rr ((κ → Rr) ⧸ Ebar r E) = finrank 𝒪 A := by
  have hrΦ : ∀ w : P, Φ (r • w) = 0 := fun w => (hΦk _).mpr (hrE w)
  let e : ((κ → Rr) ⧸ Ebar r E) ≃ₗ[Rr] (ι → Rr) :=
    (Submodule.quotEquivOfEq _ _ (ker_Phibar r Φ hrE hΦk).symm).trans
      ((Phibar r Φ).quotKerEquivOfSurjective (Phibar_surjective r Φ hrΦ hΦs))
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_chooseBasisIndex]

def Eperp (hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w)) (E : Submodule A P) : Submodule A P where
  carrier := {v | ∀ e ∈ E, β v e ∈ Ideal.span ({r} : Set 𝒪)}
  zero_mem' e he := by simp
  add_mem' {v w} hv hw e he := by
    rw [map_add, LinearMap.add_apply]
    exact Ideal.add_mem _ (hv e he) (hw e he)
  smul_mem' a v hv e he := by
    show β (a • v) e ∈ _
    rw [hbal]
    exact hv _ (E.smul_mem a he)

theorem mem_Eperp {hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w)} {E : Submodule A P} {v : P} :
    v ∈ Eperp r β hbal E ↔ ∀ e ∈ E, β v e ∈ Ideal.span ({r} : Set 𝒪) := Iff.rfl

theorem redP_mem_perp_iff (hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w)) (E : Submodule A P)
    (v : P) : redP r v ∈ perp (Bbar r β) (Ebar r E) ↔ v ∈ Eperp r β hbal E := by
  rw [mem_perp, mem_Eperp]
  constructor
  · intro h e he
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Bbar_redP]
    exact h _ ⟨e, he, rfl⟩
  · rintro h _ ⟨e, he, rfl⟩
    rw [Bbar_redP, Ideal.Quotient.eq_zero_iff_mem]
    exact h e he

end OWorld

section Cyclic

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
  {A : Type*} [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
  {P : Type*} [AddCommGroup P] [Module A P] [Module 𝒪 P] [IsScalarTower 𝒪 A P]
  [Module.Finite 𝒪 P] [Module.Free 𝒪 P]
  [DecidableEq (Module.Free.ChooseBasisIndex 𝒪 P)] [DecidableEq (Module.Free.ChooseBasisIndex 𝒪 A)]
  (r : 𝒪)
  (β : P →ₗ[𝒪] P →ₗ[𝒪] 𝒪) (hβ : Function.Bijective β)
  (hanti : ∀ v w, β v w = - β w v) (hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w))
  (E : Submodule A P) (hrE : ∀ w : P, r • w ∈ E)
  (Φ : P →ₗ[𝒪] (A →ₗ[𝒪] 𝒪 ⧸ Ideal.span ({r} : Set 𝒪))) (hΦs : Function.Surjective Φ)
  (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) (hΦa : ∀ (a : A) (v : P) (t : A), Φ (a • v) t = Φ v (a * t))

set_option quotPrecheck false in
local notation "Rr" => 𝒪 ⧸ Ideal.span (Singleton.singleton r)
set_option quotPrecheck false in
local notation "π₀" => Ideal.Quotient.mk (Ideal.span (Singleton.singleton r))
local notation "κ" => Module.Free.ChooseBasisIndex 𝒪 P
local notation "ι" => Module.Free.ChooseBasisIndex 𝒪 A
local notation "bP" => Module.Free.chooseBasis 𝒪 P
local notation "bA" => Module.Free.chooseBasis 𝒪 A

include hβ in

theorem exists_y0 : ∃ y₀ : P, ∀ w, π₀ (β y₀ w) = Φ w 1 :=
  exists_repr_functional r β hβ
    { toFun := fun w => Φ w 1
      map_add' := fun v w => by rw [map_add, LinearMap.add_apply]
      map_smul' := fun c w => by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply] }

include hbal hΦa in

theorem key_a {y₀ : P} (hy₀ : ∀ w, π₀ (β y₀ w) = Φ w 1) (a : A) (w : P) :
    π₀ (β (a • y₀) w) = Φ w a := by
  rw [hbal, hy₀, hΦa, mul_one]

include hβ hΦs hΦk in

theorem exists_a_of_mem {y : P} (hy : y ∈ Eperp r β hbal E) : ∃ a : A, ∀ w, π₀ (β y w) = Φ w a := by

  obtain ⟨βy, hβy⟩ : ∃ βy : P →ₗ[𝒪] Rr, ∀ w, βy w = π₀ (β y w) := ⟨(piL r).comp (β y), fun w => rfl⟩
  have hle : LinearMap.ker (PhiP r Φ) ≤ LinearMap.ker βy := by
    intro v hv
    rw [LinearMap.mem_ker, PhiP_eq_zero_iff r Φ hΦk] at hv
    rw [LinearMap.mem_ker, hβy, Ideal.Quotient.eq_zero_iff_mem]
    exact hy v hv
  let eΦ := (PhiP r Φ).quotKerEquivOfSurjective (PhiP_surjective r Φ hΦs)
  let θ : (ι → Rr) →ₗ[𝒪] Rr := ((LinearMap.ker (PhiP r Φ)).liftQ βy hle).comp eΦ.symm.toLinearMap
  have hθ : ∀ w, θ (PhiP r Φ w) = π₀ (β y w) := fun w => by
    show (LinearMap.ker (PhiP r Φ)).liftQ βy hle (eΦ.symm (PhiP r Φ w)) = _
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk (PhiP r Φ) (PhiP_surjective r Φ hΦs) w]
    show (LinearMap.ker (PhiP r Φ)).liftQ βy hle (eΦ.symm (eΦ (Submodule.Quotient.mk w))) = _
    rw [LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
    exact hβy w

  have hθsmul : ∀ (t : Rr) (u : ι → Rr), θ (t • u) = t * θ u := fun t u => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hcu : (Ideal.Quotient.mk (Ideal.span ({r} : Set 𝒪)) c) • u = c • u :=
      algebraMap_smul (𝒪 ⧸ Ideal.span ({r} : Set 𝒪)) c u
    rw [hcu, map_smul, base_smul_eq]

  choose c hc using fun i : ι => Ideal.Quotient.mk_surjective (θ (Pi.single i 1))
  refine ⟨∑ i, c i • (bA) i, fun w => ?_⟩

  have hR : π₀ (β y w) = ∑ i, PhiP r Φ w i * θ (Pi.single i 1) := by
    rw [← hθ]
    conv_lhs => rw [pi_eq_sum_univ' (PhiP r Φ w)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθsmul]
  have hL : Φ w (∑ i, c i • (bA) i) = ∑ i, PhiP r Φ w i * θ (Pi.single i 1) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, base_smul_eq, hc, PhiP_apply, mul_comm]
  rw [hR, hL]

include hβ hΦs hΦk hΦa in

theorem cyclic {y₀ : P} (hy₀ : ∀ w, π₀ (β y₀ w) = Φ w 1) {y : P} (hy : y ∈ Eperp r β hbal E) :
    ∃ (a : A) (w : P), y = a • y₀ + r • w := by
  obtain ⟨a, ha⟩ := exists_a_of_mem r β hβ hbal E Φ hΦs hΦk hy
  obtain ⟨w, hw⟩ := exists_eq_smul_of_forall_mem r β hβ (y - a • y₀) fun w => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, LinearMap.sub_apply, map_sub, ha,
      key_a r β hbal Φ hΦa hy₀, sub_self]
  exact ⟨a, w, by rw [← hw]; abel⟩

include hΦk in
theorem y0_mem {y₀ : P} (hy₀ : ∀ w, π₀ (β y₀ w) = Φ w 1) : y₀ ∈ Eperp r β hbal E := by
  intro e he
  rw [← Ideal.Quotient.eq_zero_iff_mem, hy₀, (hΦk e).mpr he, LinearMap.zero_apply]

include hβ hbal hΦs hΦa in

theorem ann_iff {y₀ : P} (hy₀ : ∀ w, π₀ (β y₀ w) = Φ w 1) (a : A) :
    (∃ w : P, a • y₀ = r • w) ↔ ∃ b : A, a = algebraMap 𝒪 A r * b := by
  constructor
  · rintro ⟨w, hw⟩

    have hΦa0 : ∀ w', Φ w' a = 0 := fun w' => by
      rw [← key_a r β hbal Φ hΦa hy₀, hw, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)
    have hφ : ∀ φ : A →ₗ[𝒪] Rr, φ a = 0 := fun φ => by
      obtain ⟨w', rfl⟩ := hΦs φ
      exact hΦa0 w'
    have hi : ∀ i, ∃ c : 𝒪, c * r = (bA).repr a i := fun i => by
      have := hφ ((piL r).comp ((bA).coord i))
      rw [LinearMap.comp_apply, piL_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at this
      exact this
    choose c hc using hi
    refine ⟨∑ i, c i • (bA) i, ?_⟩
    calc a = ∑ i, (bA).repr a i • (bA) i := ((bA).sum_repr a).symm
      _ = ∑ i, r • (c i • (bA) i) := Finset.sum_congr rfl fun i _ => by rw [← hc, mul_comm, mul_smul]
      _ = algebraMap 𝒪 A r * ∑ i, c i • (bA) i := by rw [← Finset.smul_sum, Algebra.smul_def]
  · rintro ⟨b, rfl⟩
    exact ⟨b • y₀, by rw [mul_smul, algebraMap_smul]⟩

include hanti hbal in

theorem self_orth (v : P) (c : A) : β v (c • v) = 0 := by
  have h1 : β (c • v) v = β v (c • v) := hbal c v v
  have h2 : β v (c • v) = - β (c • v) v := hanti v (c • v)
  rw [h1] at h2
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h2)

include hβ hanti hΦs hΦk hΦa in

theorem isotropic {y₀ : P} (hy₀ : ∀ w, π₀ (β y₀ w) = Φ w 1) {y y' : P}
    (hy : y ∈ Eperp r β hbal E) (hy' : y' ∈ Eperp r β hbal E) : β y y' ∈ Ideal.span ({r} : Set 𝒪) := by
  obtain ⟨a, w, rfl⟩ := cyclic r β hβ hbal E Φ hΦs hΦk hΦa hy₀ hy
  obtain ⟨a', w', rfl⟩ := cyclic r β hβ hbal E Φ hΦs hΦk hΦa hy₀ hy'
  have h0 : β (a • y₀) (a' • y₀) = 0 := by rw [hbal, ← mul_smul, self_orth β hanti hbal]
  have hr1 : ∀ t : 𝒪, r * t ∈ Ideal.span ({r} : Set 𝒪) := fun t =>
    Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)
  have hmem : β (a • y₀ + r • w) (a' • y₀ + r • w') =
      r * (β (a • y₀) w' + β w (a' • y₀) + r * β w w') := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h0]
    ring
  rw [hmem]
  exact hr1 _

end Cyclic

end PerfPairDuality
p2m_reactivate "P2MW.S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul.PerfPairDuality"

end
p2m_reactivate "P2MW.S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul.PerfPairDuality"

open PerfPairDuality Module in
theorem solution
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {A : Type*} [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module 𝒪 P] [IsScalarTower 𝒪 A P]
    [Module.Finite 𝒪 P] [Module.Free 𝒪 P]
    (hrank : Module.finrank 𝒪 P = 2 * Module.finrank 𝒪 A)
    (β : P →ₗ[𝒪] P →ₗ[𝒪] 𝒪) (hβ : Function.Bijective β)
    (hanti : ∀ v w, β v w = - β w v) (hbal : ∀ (a : A) (v w : P), β (a • v) w = β v (a • w))
    (r : 𝒪) (hr : r ∈ IsLocalRing.maximalIdeal 𝒪) (hr0 : r ≠ 0)
    (E : Submodule A P) (hrE : ∀ w : P, r • w ∈ E)
    (Φ : P →ₗ[𝒪] (A →ₗ[𝒪] 𝒪 ⧸ Ideal.span {r})) (hΦs : Function.Surjective Φ)
    (hΦk : ∀ v, Φ v = 0 ↔ v ∈ E) (hΦa : ∀ (a : A) (v : P) (t : A), Φ (a • v) t = Φ v (a * t)) :
    ∃ x ∈ E, (∀ v ∈ E, ∃ (a : A) (w : P), v = a • x + r • w) ∧
      (∀ a : A, (∃ w : P, a • x = r • w) ↔ ∃ b : A, a = algebraMap 𝒪 A r * b) := by
  classical

  haveI hnt : Nontrivial (𝒪 ⧸ Ideal.span ({r} : Set 𝒪)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact hr)
  haveI : IsLocalRing (𝒪 ⧸ Ideal.span ({r} : Set 𝒪)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

  obtain ⟨y₀, hy₀⟩ := exists_y0 r β hβ Φ

  have hV : finrank (𝒪 ⧸ Ideal.span ({r} : Set 𝒪))
      (Module.Free.ChooseBasisIndex 𝒪 P → 𝒪 ⧸ Ideal.span ({r} : Set 𝒪)) = 2 * finrank 𝒪 A := by
    rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_eq_card_chooseBasisIndex, hrank]
  obtain ⟨hf₁, hf₁', hd₁⟩ := free_quotient_Ebar r Φ hrE hΦs hΦk
  obtain ⟨hf₂, hf₂', hd₂⟩ := free_quotient_perp (Bbar_bijective r β hβ) (Ebar r E) hf₁ hf₁'
  rw [hd₁, hV, two_mul, Nat.add_right_cancel_iff] at hd₂
  obtain ⟨hf₃, hf₃', hd₃⟩ := free_quotient_perp (Bbar_bijective r β hβ) (perp (Bbar r β) (Ebar r E)) hf₂ hf₂'
  rw [hd₂, hV, two_mul, Nat.add_right_cancel_iff] at hd₃

  have h12 : Ebar r E ≤ perp (Bbar r β) (perp (Bbar r β) (Ebar r E)) :=
    le_perp_perp (Bbar_antisymm r β hanti) _
  have h23 : perp (Bbar r β) (Ebar r E) ≤ perp (Bbar r β) (perp (Bbar r β) (Ebar r E)) := by
    intro u hu u' hu'
    obtain ⟨y, rfl⟩ := redP_surjective r u
    obtain ⟨y', rfl⟩ := redP_surjective r u'
    rw [redP_mem_perp_iff r β hbal] at hu hu'
    rw [Bbar_redP, Ideal.Quotient.eq_zero_iff_mem]
    exact isotropic r β hβ hanti hbal E Φ hΦs hΦk hΦa hy₀ hu hu'

  have hEq23 : perp (Bbar r β) (Ebar r E) = perp (Bbar r β) (perp (Bbar r β) (Ebar r E)) :=
    eq_of_le_of_free_quotient h23 hf₂ hf₂' hf₃ hf₃' (hd₂.trans hd₃.symm)
  rw [← hEq23] at h12
  have hEq : Ebar r E = perp (Bbar r β) (Ebar r E) :=
    eq_of_le_of_free_quotient h12 hf₁ hf₁' hf₂ hf₂' (hd₁.trans hd₂.symm)

  have hEE' : ∀ v : P, v ∈ E ↔ v ∈ Eperp r β hbal E := fun v => by
    rw [← mem_Ebar_iff r hrE, hEq, redP_mem_perp_iff r β hbal]
  refine ⟨y₀, (hEE' y₀).mpr (y0_mem r β hbal E Φ hΦk hy₀), fun v hv => ?_, ann_iff r β hβ hbal Φ hΦs hΦa hy₀⟩
  exact cyclic r β hβ hbal E Φ hΦs hΦk hΦa hy₀ ((hEE' v).mp hv)

end S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul
end P2MW
export P2MW.S_Submodule_exists_generator_of_perfectPairing_antisymm_of_quotient_dual_of_finrank_eq_two_mul (solution)
