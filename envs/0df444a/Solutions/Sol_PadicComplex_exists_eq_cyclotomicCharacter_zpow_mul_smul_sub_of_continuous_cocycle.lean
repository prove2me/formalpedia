-- Prove2me | solution 1 for PadicComplex.exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/21481b49-c1d6-5ebf-aaa0-ef9b4db928b4

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
import Theorems.Thm_PadicComplex_exists_isTateTrace_cyclotomicTower
import Theorems.Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure
import Theorems.Thm_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace
import Theorems.Thm_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle

set_option autoImplicit false

noncomputable section

namespace TT2

open UniformSpace Filter Topology
open scoped Pointwise NNReal

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section tower

variable (p)

abbrev F (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := PadicAlgCl.cyclotomicTower p n

def rootSet (n : ℕ) : Set Ω := {ζ : Ω | ζ ^ (p ^ n) = 1}

lemma F_eq_adjoin (n : ℕ) : F p n = IntermediateField.adjoin ℚ_[p] (rootSet p n) := rfl

lemma rootSet_finite (n : ℕ) : (rootSet p n).Finite := by
  classical
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine (Polynomial.nthRoots (p ^ n) (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hpn]
  exact hζ

scoped instance F_finiteDimensional (n : ℕ) : FiniteDimensional ℚ_[p] (F p n) := by
  haveI : Finite (rootSet p n) := (rootSet_finite p n).to_subtype
  rw [F_eq_adjoin]
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

lemma F_mono : Monotone (F p) := PadicAlgCl.cyclotomicTower_mono p

lemma gal_mem_F (g : Γ) (n : ℕ) {y : Ω} (hy : y ∈ F p n) : g y ∈ F p n := by
  have hmap : (F p n).map (g : Ω →ₐ[ℚ_[p]] Ω) ≤ F p n := by
    rw [F_eq_adjoin, IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono ℚ_[p] _ _ ?_
    rintro _ ⟨ζ, hζ, rfl⟩
    show (g ζ) ^ (p ^ n) = 1
    rw [← map_pow, (hζ : ζ ^ (p ^ n) = 1), map_one]
  exact hmap ((IntermediateField.mem_map _).2 ⟨y, hy, rfl⟩)

lemma mem_fixingSubgroup_F_of_forall (g : Γ) (n : ℕ)
    (h : ∀ ζ : Ω, ζ ^ (p ^ n) = 1 → g ζ = ζ) : g ∈ (F p n).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [F_eq_adjoin] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap x => exact g.commutes x
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

lemma apply_eq_of_mem_fixingSubgroup {E : IntermediateField ℚ_[p] Ω} {g : Γ}
    (hg : g ∈ E.fixingSubgroup) {y : Ω} (hy : y ∈ E) : g y = y :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy

def χ (g : Γ) : ℤ_[p]ˣ := cyclotomicCharacter (PadicAlgCl p) p (g : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv

lemma toRingEquiv_mul (g h : Γ) : (g * h).toRingEquiv = g.toRingEquiv * h.toRingEquiv := rfl

lemma χ_mul (g h : Γ) : χ p (g * h) = χ p g * χ p h := by
  unfold χ; rw [toRingEquiv_mul, map_mul]

lemma χ_one : χ p 1 = 1 := by unfold χ; exact map_one _

lemma χ_pow (g : Γ) (n : ℕ) : χ p (g ^ n) = χ p g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, χ_one]
  | succ n ih => rw [pow_succ, pow_succ, χ_mul, ih]

lemma toZModPow_χ_eq_one {g : Γ} {n : ℕ} (hg : g ∈ (F p n).fixingSubgroup) :
    PadicInt.toZModPow n (χ p g : ℤ_[p]) = 1 := by
  unfold χ
  rw [cyclotomicCharacter.toZModPow]
  have hu := modularCyclotomicCharacter.unique (PadicAlgCl p)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (p ^ n))
    (g : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv (c := 1) ?_
  · rw [← hu]
  · intro t ht
    have ht' : ((t : Ωˣ) : Ω) ^ (p ^ n) = 1 := by
      have := (mem_rootsOfUnity _ t).1 ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    have hfix : g ((t : Ωˣ) : Ω) = t :=
      apply_eq_of_mem_fixingSubgroup p hg (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p ht')
    show g ((t : Ωˣ) : Ω) = _
    rw [hfix, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 (p ^ n) with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, pow_one]
    · have hpn : p ^ n = 1 := le_antisymm h1 (pow_pos (Fact.out : p.Prime).pos n)
      rw [hpn, Nat.mod_self, pow_zero]
      rw [hpn, pow_one] at ht'
      exact ht'

lemma norm_χ_sub_one_le {g : Γ} {n : ℕ} (hg : g ∈ (F p n).fixingSubgroup) :
    ‖((χ p g : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have h : (χ p g : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, toZModPow_χ_eq_one p hg,
      sub_self]
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 h
  rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] at this

lemma mem_fixingSubgroup_F_of_χ_eq_one {g : Γ} (hg : χ p g = 1) (n : ℕ) :
    g ∈ (F p n).fixingSubgroup := by
  refine mem_fixingSubgroup_F_of_forall p g n fun ζ hζ => ?_
  have h := cyclotomicCharacter.spec p (g : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv ζ hζ
  change g ζ = ζ ^ ((PadicInt.toZModPow n) (χ p g : ℤ_[p])).val at h
  rw [hg, Units.val_one, map_one, ZMod.val_one_eq_one_mod] at h
  rw [h]
  rcases Nat.lt_or_ge 1 (p ^ n) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hpn : p ^ n = 1 := le_antisymm h1 (pow_pos (Fact.out : p.Prime).pos n)
    rw [hpn, Nat.mod_self, pow_zero]
    rw [hpn, pow_one] at hζ
    exact hζ.symm

lemma χ_eq_one_of_forall {g : Γ} (hg : ∀ n, g ∈ (F p n).fixingSubgroup) : χ p g = 1 := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [toZModPow_χ_eq_one p (hg n), Units.val_one, map_one]

end tower

section cocycle

variable (p)

def Λ (k : ℤ) (σ : Γ) : ℂ_[p] :=
  (algebraMap ℚ_[p] ℂ_[p]
    (((cyclotomicCharacter (PadicAlgCl p) p (σ : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) :
      ℚ_[p])) ^ k

lemma Λ_eq (k : ℤ) (σ : Γ) : Λ p k σ = algebraMap ℚ_[p] ℂ_[p] ((((χ p σ : ℤ_[p]) : ℚ_[p])) ^ k) := by
  unfold Λ χ; rw [map_zpow₀]

lemma norm_coe_χ (σ : Γ) : ‖((χ p σ : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_units _

lemma coe_χ_ne_zero (σ : Γ) : ((χ p σ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_coe_χ]; exact one_ne_zero

lemma Λ_mul (k : ℤ) (σ τ : Γ) : Λ p k (σ * τ) = Λ p k σ * Λ p k τ := by
  rw [Λ_eq, Λ_eq, Λ_eq, χ_mul, Units.val_mul, PadicInt.coe_mul, mul_zpow, map_mul]

lemma Λ_one (k : ℤ) : Λ p k 1 = 1 := by
  rw [Λ_eq, χ_one, Units.val_one, PadicInt.coe_one, one_zpow, map_one]

lemma norm_Λ (k : ℤ) (σ : Γ) : ‖Λ p k σ‖ = 1 := by
  rw [Λ_eq, norm_algebraMap', norm_zpow, norm_coe_χ, one_zpow]

lemma Λ_ne_zero (k : ℤ) (σ : Γ) : Λ p k σ ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_Λ]; exact one_ne_zero

lemma smul_Λ (g : Γ) (k : ℤ) (σ : Γ) : g • Λ p k σ = Λ p k σ := by
  rw [Λ_eq, PadicComplex.smul_algebraMap]

lemma Λ_eq_one_of_χ {k : ℤ} {σ : Γ} (h : χ p σ = 1) : Λ p k σ = 1 := by
  rw [Λ_eq, h, Units.val_one, PadicInt.coe_one, one_zpow, map_one]

lemma continuous_Λ (k : ℤ) : Continuous (Λ p k) := by
  have h1 : Continuous fun σ : Γ => (χ p σ : ℤ_[p]) := by
    have := cyclotomicCharacter.continuous p ℚ_[p] (PadicAlgCl p)
    exact Units.continuous_val.comp this
  have h2 : Continuous fun σ : Γ => (((χ p σ : ℤ_[p]) : ℚ_[p])) :=
    continuous_subtype_val.comp h1
  have h3 : Continuous fun σ : Γ => (((χ p σ : ℤ_[p]) : ℚ_[p])) ^ k :=
    h2.zpow₀ k fun σ => Or.inl (coe_χ_ne_zero p σ)
  have h4 := (continuous_algebraMap ℚ_[p] ℂ_[p]).comp h3
  convert h4 using 1
  ext σ; exact Λ_eq p k σ

def IsCoc (G : Subgroup Γ) (k : ℤ) (c : G → ℂ_[p]) : Prop :=
  ∀ σ τ : G, c (σ * τ) = c σ + Λ p k σ * ((σ : Γ) • c τ)

def cob (G : Subgroup Γ) (k : ℤ) (b : ℂ_[p]) : G → ℂ_[p] := fun σ => Λ p k σ * ((σ : Γ) • b) - b

variable {p}
variable {G : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {k : ℤ}

lemma isCoc_cob (b : ℂ_[p]) : IsCoc p G k (cob p G k b) := by
  intro σ τ
  simp only [cob, Subgroup.coe_mul, Λ_mul, mul_smul, smul_sub, smul_mul', smul_Λ]
  ring

lemma IsCoc.sub {c c' : G → ℂ_[p]} (hc : IsCoc p G k c) (hc' : IsCoc p G k c') :
    IsCoc p G k (c - c') := by
  intro σ τ
  simp only [Pi.sub_apply, hc σ τ, hc' σ τ, smul_sub]
  ring

lemma IsCoc.map_one {c : G → ℂ_[p]} (hc : IsCoc p G k c) : c 1 = 0 := by
  have := hc 1 1
  rw [mul_one, Subgroup.coe_one, Λ_one, one_smul, one_mul] at this
  linear_combination -this

lemma IsCoc.apply_mul_of_left {c : G → ℂ_[p]} (hc : IsCoc p G k c) {σ : G} (hσ : c σ = 0) (τ : G) :
    c (σ * τ) = Λ p k σ * ((σ : Γ) • c τ) := by rw [hc, hσ, zero_add]

lemma IsCoc.apply_mul_of_right {c : G → ℂ_[p]} (hc : IsCoc p G k c) (σ : G) {τ : G} (hτ : c τ = 0) :
    c (σ * τ) = c σ := by rw [hc, hτ, smul_zero, mul_zero, add_zero]

lemma IsCoc.norm_apply_mul_of_left {c : G → ℂ_[p]} (hc : IsCoc p G k c) {σ : G} (hσ : c σ = 0)
    (τ : G) : ‖c (σ * τ)‖ = ‖c τ‖ := by
  rw [hc.apply_mul_of_left hσ, norm_mul, norm_Λ, one_mul, PadicComplex.norm_smul_eq]

lemma IsCoc.apply_pow {c : G → ℂ_[p]} (hc : IsCoc p G k c) {σ : G} (hσ : c σ = 0) (n : ℕ) :
    c (σ ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero]; exact hc.map_one
  | succ n ih => rw [pow_succ, hc.apply_mul_of_right _ hσ, ih]

lemma cob_add (b b' : ℂ_[p]) : cob p G k (b + b') = cob p G k b + cob p G k b' := by
  ext σ; simp only [cob, Pi.add_apply, smul_add]; ring

lemma continuous_orbit (b : ℂ_[p]) : Continuous fun σ : Γ => σ • b := by
  refine continuous_iff_continuousAt.2 fun σ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := Ω)) b ε hε
  let E : IntermediateField ℚ_[p] Ω := IntermediateField.adjoin ℚ_[p] {a}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hU : IsOpen (E.fixingSubgroup : Set Γ) := IntermediateField.fixingSubgroup_isOpen E
  have hV : IsOpen {x : Γ | σ⁻¹ * x ∈ E.fixingSubgroup} :=
    hU.preimage (continuous_const_mul σ⁻¹)
  have hσV : σ ∈ {x : Γ | σ⁻¹ * x ∈ E.fixingSubgroup} := by
    show σ⁻¹ * σ ∈ E.fixingSubgroup; rw [inv_mul_cancel]; exact Subgroup.one_mem _
  filter_upwards [hV.mem_nhds hσV] with x hx
  set u := σ⁻¹ * x with hu
  have hxu : x = σ * u := by rw [hu, mul_inv_cancel_left]
  have hua : u • ((a : Ω) : ℂ_[p]) = (a : ℂ_[p]) := by
    rw [PadicComplex.smul_coe, apply_eq_of_mem_fixingSubgroup p hx
      (IntermediateField.mem_adjoin_simple_self ℚ_[p] a)]
  rw [dist_eq_norm, hxu, mul_smul, ← smul_sub, PadicComplex.norm_smul_eq]
  have : u • b - b = u • (b - a) - (b - a) := by rw [smul_sub, hua]; abel
  rw [this]
  calc ‖u • (b - ↑a) - (b - ↑a)‖ ≤ max ‖u • (b - ↑a)‖ ‖-(b - ↑a)‖ := by
        rw [sub_eq_add_neg]; exact IsUltrametricDist.norm_add_le_max _ _
    _ = ‖b - ↑a‖ := by rw [norm_neg, PadicComplex.norm_smul_eq, max_self]
    _ < ε := by rwa [← dist_eq_norm]

lemma continuous_cob (b : ℂ_[p]) : Continuous (cob p G k b) := by
  unfold cob
  exact (((continuous_Λ p k).comp continuous_subtype_val).mul
    ((continuous_orbit b).comp continuous_subtype_val)).sub continuous_const

end cocycle

section gen

variable (p)

abbrev Fm (m : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := F p (m + 2)

lemma Fm_def (m : ℕ) : Fm p m = F p (m + 2) := rfl

lemma Fm_mono : Monotone (Fm p) := fun a b hab => F_mono p (by omega)

def IsGen (m : ℕ) (σ : Γ) : Prop :=
  σ ∈ (Fm p m).fixingSubgroup ∧ σ ∉ (Fm p (m + 1)).fixingSubgroup

lemma hcyc (m : ℕ) (σ : Γ) (h1 : σ ∈ (Fm p m).fixingSubgroup)
    (h2 : σ ∉ (Fm p (m + 1)).fixingSubgroup) :
    σ ^ p ∈ (Fm p (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Fm p (m + 2)).fixingSubgroup :=
  (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).2 m σ h1 h2

lemma finrank_Fm (m : ℕ) : Module.finrank ℚ_[p] (Fm p m) = (p - 1) * p ^ (m + 1) := by
  have h := (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 (m + 2) (by omega)
  rw [show m + 2 - 1 = m + 1 by omega] at h
  exact h

lemma finrank_Fm_succ (m : ℕ) :
    Module.finrank ℚ_[p] (Fm p (m + (1 : ℕ))) = p * Module.finrank ℚ_[p] (Fm p m) := by
  rw [finrank_Fm, finrank_Fm, pow_succ]
  ring

variable {p}

lemma isGen_pow {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) (j : ℕ) : IsGen p (m + j) (σ ^ (p ^ j)) := by
  induction j with
  | zero => simpa using hσ
  | succ j ih =>
      have h := hcyc p (m + j) _ ih.1 ih.2
      refine ⟨?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h.1
      · rw [pow_succ, pow_mul]; exact h.2

lemma pow_mem_fixingSubgroup_succ_iff {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) (i : ℕ) :
    σ ^ i ∈ (Fm p (m + 1)).fixingSubgroup ↔ p ∣ i := by
  constructor
  · intro hi
    by_contra hpi
    have hcop : Nat.Coprime i p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpi)
    obtain ⟨a, ha⟩ : ∃ a : ℕ, i * a % p = 1 := by
      obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Fact.out : p.Prime).one_lt
      exact ⟨a, ha⟩
    have hdiv : a * i = p * (a * i / p) + 1 := by
      have := Nat.div_add_mod (a * i) p
      rw [mul_comm] at ha
      omega
    apply hσ.2
    have h1 : σ ^ (a * i) ∈ (Fm p (m + 1)).fixingSubgroup := by
      rw [mul_comm, pow_mul]; exact Subgroup.pow_mem _ hi a
    have h2 : σ ^ (p * (a * i / p)) ∈ (Fm p (m + 1)).fixingSubgroup := by
      rw [pow_mul]; exact Subgroup.pow_mem _ (hcyc p m σ hσ.1 hσ.2).1 _
    rw [hdiv, pow_add, pow_one] at h1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    simpa using this
  · rintro ⟨k, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ (hcyc p m σ hσ.1 hσ.2).1 k

lemma zpow_mem_fixingSubgroup_succ_iff {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) (z : ℤ) :
    σ ^ z ∈ (Fm p (m + 1)).fixingSubgroup ↔ (p : ℤ) ∣ z := by
  rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, pow_mem_fixingSubgroup_succ_iff hσ, Int.natCast_dvd_natCast]
  · rw [zpow_neg, zpow_natCast, inv_mem_iff, pow_mem_fixingSubgroup_succ_iff hσ,
      Int.dvd_neg, Int.natCast_dvd_natCast]

lemma exists_pow_not_mem {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {i : ℕ} (hi : 0 < i) :
    ∃ n, σ ^ i ∉ (Fm p n).fixingSubgroup := by
  induction i using Nat.strong_induction_on generalizing m σ with
  | _ i ih =>
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      have hj : 0 < j := Nat.pos_of_mul_pos_left hi
      have hlt : j < p * j := lt_mul_left hj (Fact.out : p.Prime).one_lt
      have hg : IsGen p (m + 1) (σ ^ p) := by simpa using isGen_pow hσ 1
      obtain ⟨n, hn⟩ := ih j hlt hg hj
      exact ⟨n, by rwa [pow_mul]⟩
    · exact ⟨m + 1, fun h => hpi ((pow_mem_fixingSubgroup_succ_iff hσ i).1 h)⟩

lemma χ_zpow_ne_one {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {k : ℤ} (hk : k ≠ 0) :
    (χ p σ) ^ k ≠ 1 := by
  have key : ∀ i : ℕ, 0 < i → χ p σ ^ i ≠ 1 := by
    intro i hi h
    obtain ⟨n, hn⟩ := exists_pow_not_mem hσ hi
    exact hn (mem_fixingSubgroup_F_of_χ_eq_one p (by rw [χ_pow, h]) (n + 2))
  rcases Int.eq_nat_or_neg k with ⟨i, rfl | rfl⟩
  · have hi : 0 < i := by omega
    rw [zpow_natCast]; exact key i hi
  · have hi : 0 < i := by omega
    rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]; exact key i hi

variable (p)

lemma index_Fm (m : ℕ) : (Fm p m).fixingSubgroup.index = Module.finrank ℚ_[p] (Fm p m) :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (L := Fm p m)).symm

lemma relIndex_Fm (m : ℕ) :
    (Fm p (m + 1)).fixingSubgroup.relIndex (Fm p m).fixingSubgroup = p := by
  have hle : (Fm p (m + 1)).fixingSubgroup ≤ (Fm p m).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fm_mono p (Nat.le_succ m))
  have h := Subgroup.relIndex_mul_index hle
  rw [index_Fm, index_Fm, finrank_Fm_succ] at h
  have hpos : Module.finrank ℚ_[p] (Fm p m) ≠ 0 := Module.finrank_pos.ne'
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h

variable {p}

lemma exists_pow_inv_mul_mem {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {τ : Γ}
    (hτ : τ ∈ (Fm p m).fixingSubgroup) :
    ∃ i : ℕ, (σ ^ i)⁻¹ * τ ∈ (Fm p (m + 1)).fixingSubgroup := by
  classical
  set H : Subgroup Γ := (Fm p m).fixingSubgroup with hH
  set H' : Subgroup Γ := (Fm p (m + 1)).fixingSubgroup with hH'
  set Q := H ⧸ H'.subgroupOf H with hQ
  have hcard : Nat.card Q = p := relIndex_Fm p m
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)
  let s : H := ⟨σ, hσ.1⟩
  let f : Fin p → Q := fun i => QuotientGroup.mk (s ^ (i : ℕ))
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : (s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) ∈ H'.subgroupOf H := QuotientGroup.eq.mp hij
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((s ^ (i : ℕ))⁻¹ * s ^ (j : ℕ) : H) = (s ^ ((j : ℤ) - (i : ℤ)) : H) := by
      rw [zpow_sub, zpow_natCast, zpow_natCast]
      exact (Commute.pow_pow_self s i j).inv_left.eq.trans (by group)
    rw [h2] at h1
    have h3 : (((s ^ ((j : ℤ) - (i : ℤ)) : H) : Γ)) = σ ^ ((j : ℤ) - (i : ℤ)) := by
      simp [s]
    rw [h3, zpow_mem_fixingSubgroup_succ_iff hσ] at h1
    have h4 : ((j : ℤ) - (i : ℤ)) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h1
      have hi := i.2; have hj := j.2
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)
  have hbij := hf.bijective_of_nat_card_le (by simp [hcard])
  obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk ⟨τ, hτ⟩)
  refine ⟨i, ?_⟩
  have h1 : (s ^ (i : ℕ))⁻¹ * ⟨τ, hτ⟩ ∈ H'.subgroupOf H := QuotientGroup.eq.mp hi
  rw [Subgroup.mem_subgroupOf] at h1
  simpa [s] using h1

lemma exists_pow_inv_mul_mem_add {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {τ : Γ}
    (hτ : τ ∈ (Fm p m).fixingSubgroup) (n : ℕ) :
    ∃ i : ℕ, (σ ^ i)⁻¹ * τ ∈ (Fm p (m + n)).fixingSubgroup := by
  induction n with
  | zero => exact ⟨0, by simpa using hτ⟩
  | succ n ih =>
      obtain ⟨i, hi⟩ := ih
      have hg : IsGen p (m + n) (σ ^ (p ^ n)) := isGen_pow hσ n
      obtain ⟨j, hj⟩ := exists_pow_inv_mul_mem hg hi
      refine ⟨i + p ^ n * j, ?_⟩
      rw [show m + (n + 1) = m + n + 1 by ring]
      convert hj using 1
      rw [← pow_mul, pow_add, mul_inv_rev, mul_assoc]

variable (p)

lemma exists_isGen_mem (K : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] K] (m₀ : ℕ) :
    ∃ m, m₀ ≤ m ∧ ∃ σ ∈ K.fixingSubgroup, IsGen p m σ := by
  by_contra hcon
  push Not at hcon

  have hstep : ∀ j, K.fixingSubgroup ⊓ (Fm p m₀).fixingSubgroup ≤ (Fm p (m₀ + j)).fixingSubgroup := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro τ hτ
        have h1 : τ ∈ (Fm p (m₀ + j)).fixingSubgroup := ih hτ
        by_contra h2
        exact hcon (m₀ + j) (by omega) τ hτ.1 ⟨h1, by rwa [show m₀ + (j + 1) = m₀ + j + 1 by ring] at h2⟩
  have hle : ∀ j, Fm p (m₀ + j) ≤ K ⊔ Fm p m₀ := by
    intro j
    have h := hstep j
    rw [← IntermediateField.fixingSubgroup_sup] at h
    have := (IntermediateField.le_iff_le _ _).2 h
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at this

  have hfin : ∀ j, Module.finrank ℚ_[p] (Fm p (m₀ + j)) ≤
      Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Fm p m₀) := by
    intro j
    haveI : FiniteDimensional ℚ_[p] (K ⊔ Fm p m₀ : IntermediateField ℚ_[p] Ω) :=
      IntermediateField.finiteDimensional_sup K (Fm p m₀)
    exact (IntermediateField.finrank_le_of_le_right (hle j)).trans
      (IntermediateField.finrank_sup_le K (Fm p m₀))

  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set A := Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Fm p m₀) with hA
  have h := hfin A
  rw [finrank_Fm] at h
  have h1 : p ^ (m₀ + A + 1) ≤ A := by
    calc p ^ (m₀ + A + 1) ≤ (p - 1) * p ^ (m₀ + A + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ A := h
  have h2 : A < p ^ A := Nat.lt_pow_self hp1
  have h3 : p ^ A ≤ p ^ (m₀ + A + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end gen

section traces

variable (p)

lemma exists_traces :
    ∃ d : ℝ, 0 < d ∧ ∀ m, ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p (Fm p) m d R :=
  PadicComplex.exists_isTateTrace_cyclotomicTower p

end traces

section span

variable (p)

def Finf : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n : ℕ, F p n

lemma F_le_Finf (n : ℕ) : F p n ≤ Finf p := le_iSup (F p) n

lemma coe_Finf : (Finf p : Set Ω) = ⋃ n, (F p n : Set Ω) :=
  IntermediateField.coe_iSup_of_directed (F_mono p).directed_le

def SF : Subfield ℂ_[p] := (Finf p).toSubfield.map (algebraMap Ω ℂ_[p])

def XF : Subfield ℂ_[p] := (SF p).topologicalClosure

lemma coe_XF_eq_closure : (XF p : Set ℂ_[p]) = closure (SF p : Set ℂ_[p]) := rfl

lemma coe_SF : (SF p : Set ℂ_[p]) = ⋃ m, Set.range fun k : Fm p m => ((k : Ω) : ℂ_[p]) := by
  ext x
  simp only [SF, Subfield.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ (Finf p : Set Ω) := hy
    rw [coe_Finf, Set.mem_iUnion] at hy'
    obtain ⟨n, hn⟩ := hy'
    exact ⟨n, ⟨y, F_mono p (by omega) hn⟩, rfl⟩
  · rintro ⟨m, k, rfl⟩
    exact ⟨(k : Ω), (F_le_Finf p (m + 2) k.2 : (k : Ω) ∈ Finf p), rfl⟩

lemma coe_XF : (XF p : Set ℂ_[p]) = PadicComplex.towerClosure p (Fm p) := by
  rw [coe_XF_eq_closure, coe_SF]; rfl

lemma coe_XF' : (XF p : Set ℂ_[p]) = closure (Set.range fun k : Finf p => ((k : Ω) : ℂ_[p])) := by
  rw [coe_XF_eq_closure]
  congr 1
  ext x
  simp only [SF, Subfield.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, k.2, rfl⟩

lemma algebraMap_mem_XF (q : ℚ_[p]) : algebraMap ℚ_[p] ℂ_[p] q ∈ XF p := by
  refine Subfield.le_topologicalClosure _ ?_
  refine ⟨algebraMap ℚ_[p] Ω q, ?_, (IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p] q).symm⟩
  exact (Finf p).algebraMap_mem q

scoped instance XF.normedField : NormedField (XF p) :=
  NormedField.induced (XF p) ℂ_[p] (XF p).subtype Subtype.val_injective

p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"
lemma XF.norm_def (x : XF p) : ‖x‖ = ‖(x : ℂ_[p])‖ := rfl

scoped instance XF.nontriviallyNormedField : NontriviallyNormedField (XF p) where
  toNormedField := XF.normedField p
  non_trivial := by
    refine ⟨⟨algebraMap ℚ_[p] ℂ_[p] ((p : ℚ_[p]))⁻¹, algebraMap_mem_XF p _⟩, ?_⟩
    show 1 < ‖algebraMap ℚ_[p] ℂ_[p] ((p : ℚ_[p]))⁻¹‖
    rw [norm_algebraMap', norm_inv, Padic.norm_p, inv_inv]
    exact_mod_cast (Fact.out : p.Prime).one_lt

p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"
scoped instance XF.completeSpace : @CompleteSpace (XF p) (XF.normedField p).toUniformSpace := by
  have : CompleteSpace (XF p) :=
    letI : IsClosed ((XF p : Set ℂ_[p])) := Subfield.isClosed_topologicalClosure _
    IsClosed.completeSpace_coe
  exact this

p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"
scoped instance XF.continuousSMul :
    @ContinuousSMul (XF p) ℂ_[p] _ (XF.normedField p).toUniformSpace.toTopologicalSpace _ := by
  have : ContinuousSMul (XF p) ℂ_[p] := ⟨by
    show Continuous fun q : XF p × ℂ_[p] => (q.1 : ℂ_[p]) * q.2
    fun_prop⟩
  exact this

p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"
lemma XF.smul_def (s : XF p) (x : ℂ_[p]) : s • x = (s : ℂ_[p]) * x := rfl

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

def eK : Fin (Module.finrank ℚ_[p] K) → ℂ_[p] := fun i => ((Module.finBasis ℚ_[p] K i : Ω) : ℂ_[p])

def TK : Submodule (XF p) ℂ_[p] := Submodule.span (XF p) (Set.range (eK p K))

scoped instance TK_finiteDimensional : FiniteDimensional (XF p) (TK p K) :=
  FiniteDimensional.span_of_finite _ (Set.finite_range _)

lemma isClosed_TK : IsClosed (TK p K : Set ℂ_[p]) := (TK p K).closed_of_finiteDimensional

def Kinf : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ Finf p

omit [FiniteDimensional ℚ_[p] K] in
lemma Kinf_def : Kinf p K = K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n := rfl

def φK : K →ₗ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] Ω ℂ_[p]).toLinearMap.comp K.val.toLinearMap

omit [FiniteDimensional ℚ_[p] K] in
lemma φK_apply (k : K) : φK p K k = ((k : Ω) : ℂ_[p]) := rfl

lemma coe_mul_mem_TK (k : K) {f : ℂ_[p]} (hf : f ∈ XF p) :
    ((k : Ω) : ℂ_[p]) * f ∈ TK p K := by
  set b := Module.finBasis ℚ_[p] K
  have hy' : ((k : Ω) : ℂ_[p]) = ∑ i, algebraMap ℚ_[p] ℂ_[p] (b.repr k i) * eK p K i := by
    have h := congrArg (φK p K) (b.sum_repr k)
    rw [map_sum, φK_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, φK_apply, Algebra.smul_def]
    rfl
  rw [hy', Finset.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : algebraMap ℚ_[p] ℂ_[p] (b.repr k i) * eK p K i * f =
      (⟨algebraMap ℚ_[p] ℂ_[p] (b.repr k i) * f,
        Subfield.mul_mem _ (algebraMap_mem_XF p _) hf⟩ : XF p) • eK p K i := by
    rw [XF.smul_def]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma coe_mem_TK_of_mem_Kinf {x : Ω} (hx : x ∈ Kinf p K) : (x : ℂ_[p]) ∈ TK p K := by
  have hx' : x ∈ (Kinf p K).toSubalgebra := hx
  rw [Kinf, IntermediateField.sup_toSubalgebra_of_isAlgebraic_left, ← IntermediateField.range_val,
    ← IntermediateField.range_val, ← Algebra.TensorProduct.productMap_range] at hx'
  rw [AlgHom.mem_range] at hx'
  obtain ⟨t, rfl⟩ := hx'
  clear hx
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact (TK p K).zero_mem
  | tmul k f =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, IntermediateField.coe_val,
        IntermediateField.coe_val]
      rw [show (((k : Ω) * (f : Ω) : Ω) : ℂ_[p]) = (k : ℂ_[p]) * ((f : Ω) : ℂ_[p]) from
        map_mul (algebraMap Ω ℂ_[p]) _ _]
      refine coe_mul_mem_TK p K k (Subfield.le_topologicalClosure _ ?_)
      exact ⟨f, f.2, rfl⟩
  | add a b ha hb =>
      rw [map_add]
      rw [show ((_ + _ : Ω) : ℂ_[p]) = _ from map_add (algebraMap Ω ℂ_[p]) _ _]
      exact (TK p K).add_mem ha hb

lemma closure_Kinf_subset_TK :
    closure (Set.range fun k : Kinf p K => ((k : Ω) : ℂ_[p])) ⊆ (TK p K : Set ℂ_[p]) := by
  refine closure_minimal ?_ (isClosed_TK p K)
  rintro _ ⟨k, rfl⟩
  exact coe_mem_TK_of_mem_Kinf p K k.2

lemma exists_coords_of_mem_TK {x : ℂ_[p]} (hx : x ∈ TK p K) :
    ∃ s : Fin (Module.finrank ℚ_[p] K) → ℂ_[p], (∀ i, s i ∈ XF p) ∧ x = ∑ i, eK p K i * s i := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (XF p)).1 hx
  refine ⟨fun i => (c i : ℂ_[p]), fun i => (c i).2, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [XF.smul_def, mul_comm]

lemma smul_eK {g : Γ} (hg : g ∈ K.fixingSubgroup) (i : Fin (Module.finrank ℚ_[p] K)) :
    g • eK p K i = eK p K i := by
  unfold eK
  rw [PadicComplex.smul_coe, apply_eq_of_mem_fixingSubgroup p hg (Module.finBasis ℚ_[p] K i).2]

end span
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"

section propagate

variable (p)
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance compactSpace_fixingSubgroup : CompactSpace K.fixingSubgroup :=
  isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K).isCompact

variable {p K}
variable {k : ℤ} {c : K.fixingSubgroup → ℂ_[p]}

lemma vanish_of_gen (hc : IsCoc p K.fixingSubgroup k c) (hcont : Continuous c)
    (hH : ∀ τ : K.fixingSubgroup, (∀ n, (τ : Γ) ∈ (F p n).fixingSubgroup) → c τ = 0)
    {m : ℕ} {σ₀ : K.fixingSubgroup} (hσ₀ : IsGen p m (σ₀ : Γ)) (h0 : c σ₀ = 0)
    (τ : K.fixingSubgroup) (hτ : (τ : Γ) ∈ (Fm p m).fixingSubgroup) : c τ = 0 := by

  have hnorm : ∀ n, ∃ ρ : K.fixingSubgroup, (ρ : Γ) ∈ (Fm p (m + n)).fixingSubgroup ∧
      ‖c τ‖ = ‖c ρ‖ := by
    intro n
    obtain ⟨i, hi⟩ := exists_pow_inv_mul_mem_add hσ₀ hτ n
    refine ⟨(σ₀ ^ i)⁻¹ * τ, by simpa using hi, ?_⟩
    have h1 : τ = σ₀ ^ i * ((σ₀ ^ i)⁻¹ * τ) := by group
    conv_lhs => rw [h1]
    exact hc.norm_apply_mul_of_left (hc.apply_pow h0 i) _

  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ ρ : K.fixingSubgroup,
      (ρ : Γ) ∈ (Fm p (m + n)).fixingSubgroup → ‖c ρ‖ < ε := by
    intro ε hε
    let U : Set K.fixingSubgroup := {ρ | ‖c ρ‖ < ε}
    have hU : IsOpen U := isOpen_lt (continuous_norm.comp hcont) continuous_const
    let Z : ℕ → Set K.fixingSubgroup := fun n =>
      {ρ | (ρ : Γ) ∈ (Fm p (m + n)).fixingSubgroup} \ U
    have hZc : ∀ n, IsClosed (Z n) := fun n =>
      ((InfiniteGalois.fixingSubgroup_isClosed (Fm p (m + n))).preimage
        continuous_subtype_val).sdiff hU
    have hZd : Directed (fun x y => x ⊇ y) Z := by
      intro a b
      refine ⟨max a b, ?_, ?_⟩
      · rintro ρ ⟨h1, h2⟩
        exact ⟨IntermediateField.fixingSubgroup_antitone (Fm_mono p (by omega)) h1, h2⟩
      · rintro ρ ⟨h1, h2⟩
        exact ⟨IntermediateField.fixingSubgroup_antitone (Fm_mono p (by omega)) h1, h2⟩
    have hZe : (Set.univ : Set K.fixingSubgroup) ∩ ⋂ n, Z n = ∅ := by
      rw [Set.univ_inter, Set.eq_empty_iff_forall_notMem]
      intro ρ hρ
      rw [Set.mem_iInter] at hρ
      have hall : ∀ n, (ρ : Γ) ∈ (F p n).fixingSubgroup := fun n =>
        IntermediateField.fixingSubgroup_antitone (F_mono p (by omega : n ≤ m + n + 2)) (hρ n).1
      have := (hρ 0).2
      exact this (by show ‖c ρ‖ < ε; rw [hH ρ hall, norm_zero]; exact hε)
    obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_family_closed Z hZc hZe hZd
    refine ⟨n, fun ρ hρ => ?_⟩
    by_contra hlt
    have : ρ ∈ (Set.univ : Set K.fixingSubgroup) ∩ Z n := ⟨Set.mem_univ _, hρ, hlt⟩
    rw [hn] at this
    exact this

  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  obtain ⟨n, hn⟩ := hsmall ε hε
  obtain ⟨ρ, hρ, hτρ⟩ := hnorm n
  rw [hτρ, zero_add]
  exact hn ρ hρ

end propagate
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"

section average

variable {G : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {k : ℤ}

lemma smul_natCast_inv (σ : Γ) (n : ℕ) : σ • ((n : ℂ_[p])⁻¹) = ((n : ℂ_[p]))⁻¹ := by
  rw [smul_inv'', ← map_natCast (algebraMap ℚ_[p] ℂ_[p]) n, PadicComplex.smul_algebraMap]

lemma exists_eq_cob_of_vanish {c : G → ℂ_[p]} (hc : IsCoc p G k c) (N : Subgroup G)
    [N.FiniteIndex] (hN : ∀ τ ∈ N, c τ = 0) : ∃ b, c = cob p G k b := by
  classical
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ N) with hn
  have hn0 : (n : ℂ_[p]) ≠ 0 := by
    have : 0 < n := Fintype.card_pos
    exact_mod_cast this.ne'

  have hconst : ∀ (σ : G) (q : G ⧸ N), c (σ * q.out) = c (σ • q).out := by
    intro σ q
    have h1 : (σ • q : G ⧸ N) = QuotientGroup.mk (σ * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (σ * q.out)
    rw [h1, hh, hc.apply_mul_of_right _ (hN _ h.2)]
  refine ⟨-((n : ℂ_[p])⁻¹ * ∑ q : G ⧸ N, c q.out), funext fun σ => ?_⟩
  simp only [cob]
  have hsum : (σ : Γ) • (∑ q : G ⧸ N, c q.out) = ∑ q : G ⧸ N, (σ : Γ) • c q.out :=
    Finset.smul_sum
  rw [smul_neg, smul_mul', smul_natCast_inv, hsum, Finset.mul_sum, mul_neg, Finset.mul_sum]
  have hterm : ∀ q : G ⧸ N, Λ p k σ * ((n : ℂ_[p])⁻¹ * (σ : Γ) • c q.out) =
      (n : ℂ_[p])⁻¹ * (c (σ • q).out - c σ) := by
    intro q
    have := hc σ q.out
    rw [hconst] at this
    rw [this]; ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← hn,
    nsmul_eq_mul]
  have hre : ∑ q : G ⧸ N, c (σ • q).out = ∑ q : G ⧸ N, c q.out :=
    Equiv.sum_comp (MulAction.toPerm (σ : G)) (fun q : G ⧸ N => c q.out)
  rw [hre]
  field_simp
  ring

end average
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"

section values

variable (p)
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

omit [FiniteDimensional ℚ_[p] K] in
lemma fixingSubgroup_Kinf_le : (Kinf p K).fixingSubgroup ≤ K.fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone le_sup_left

omit [FiniteDimensional ℚ_[p] K] in
lemma mem_fixingSubgroup_F_of_mem_Kinf {τ : Γ} (hτ : τ ∈ (Kinf p K).fixingSubgroup) (n : ℕ) :
    τ ∈ (F p n).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone ((F_le_Finf p n).trans le_sup_right) hτ

omit [FiniteDimensional ℚ_[p] K] in
lemma mem_fixingSubgroup_Finf_of_mem_Kinf {τ : Γ} (hτ : τ ∈ (Kinf p K).fixingSubgroup) :
    τ ∈ (Finf p).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone le_sup_right hτ

omit [FiniteDimensional ℚ_[p] K] in

lemma gal_mem_Kinf {g : Γ} (hg : g ∈ K.fixingSubgroup) {x : Ω} (hx : x ∈ Kinf p K) :
    g x ∈ Kinf p K := by
  have hmap : (Kinf p K).map (g : Ω →ₐ[ℚ_[p]] Ω) ≤ Kinf p K := by
    unfold Kinf Finf
    rw [IntermediateField.map_sup, IntermediateField.map_iSup]
    refine sup_le_sup ?_ (iSup_mono fun n => ?_)
    · rintro _ ⟨y, hy, rfl⟩
      show g y ∈ K
      rwa [apply_eq_of_mem_fixingSubgroup p hg hy]
    · rintro _ ⟨y, hy, rfl⟩
      exact gal_mem_F p g n hy
  exact hmap ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)

omit [FiniteDimensional ℚ_[p] K] in

lemma conj_mem_fixingSubgroup_Kinf {g : Γ} (hg : g ∈ K.fixingSubgroup) {τ : Γ}
    (hτ : τ ∈ (Kinf p K).fixingSubgroup) : g⁻¹ * τ * g ∈ (Kinf p K).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, apply_eq_of_mem_fixingSubgroup p hτ
    (gal_mem_Kinf p K hg hx), ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

variable {p K}
variable {k : ℤ} {c : K.fixingSubgroup → ℂ_[p]}

omit [FiniteDimensional ℚ_[p] K] in

lemma smul_apply_eq_of_vanish (hc : IsCoc p K.fixingSubgroup k c)
    (hH : ∀ τ : K.fixingSubgroup, (τ : Γ) ∈ (Kinf p K).fixingSubgroup → c τ = 0)
    (σ : K.fixingSubgroup) {τ : Γ} (hτ : τ ∈ (Kinf p K).fixingSubgroup) : τ • c σ = c σ := by
  let τ' : K.fixingSubgroup := ⟨τ, fixingSubgroup_Kinf_le p K hτ⟩
  have h1 : c (τ' * σ) = τ • c σ := by
    rw [hc.apply_mul_of_left (hH τ' hτ),
      Λ_eq_one_of_χ p (χ_eq_one_of_forall p (mem_fixingSubgroup_F_of_mem_Kinf p K hτ)), one_mul]
  have h2 : c (τ' * σ) = c σ := by
    have h3 : τ' * σ = σ * (σ⁻¹ * τ' * σ) := by group
    rw [h3, hc.apply_mul_of_right]
    exact hH _ (conj_mem_fixingSubgroup_Kinf p K σ.2 hτ)
  rw [← h1, h2]

lemma apply_mem_TK_of_vanish (hc : IsCoc p K.fixingSubgroup k c)
    (hH : ∀ τ : K.fixingSubgroup, (τ : Γ) ∈ (Kinf p K).fixingSubgroup → c τ = 0)
    (σ : K.fixingSubgroup) : c σ ∈ TK p K := by
  have h := (PadicComplex.forall_smul_eq_self_iff_mem_closure p (Kinf p K) (c σ)).1
    fun τ hτ => smul_apply_eq_of_vanish hc hH σ hτ
  exact closure_Kinf_subset_TK p K h

end values
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF"

lemma norm_zpow_sub_one_le {υ : ℚ_[p]} (hυ : ‖υ‖ = 1) (k : ℤ) : ‖υ ^ k - 1‖ ≤ ‖υ - 1‖ := by
  have hnat : ∀ n : ℕ, ‖υ ^ n - 1‖ ≤ ‖υ - 1‖ := by
    intro n
    rw [← geom_sum_mul υ n, norm_mul]
    have hs : ‖∑ i ∈ Finset.range n, υ ^ i‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
        rw [norm_pow, hυ, one_pow]
    calc ‖∑ i ∈ Finset.range n, υ ^ i‖ * ‖υ - 1‖ ≤ 1 * ‖υ - 1‖ :=
          mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = ‖υ - 1‖ := one_mul _
  have hυ0 : υ ≠ 0 := by rw [← norm_ne_zero_iff, hυ]; exact one_ne_zero
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact hnat n
  · have h : υ ^ (-(n : ℤ)) - 1 = -(υ ^ (-(n : ℤ))) * (υ ^ n - 1) := by
      rw [zpow_neg, zpow_natCast]
      field_simp
      ring
    rw [h, norm_mul, norm_neg, norm_zpow, hυ, one_zpow, one_mul]
    exact hnat n

end TT2
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2"

open TT2 in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (k : ℤ) (hk : k ≠ 0) (c : K.fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : K.fixingSubgroup,
      c (σ * τ) = c σ + (algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p
            (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k *
          ((σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ)) :
    ∃ b : ℂ_[p], ∀ σ : K.fixingSubgroup,
      c σ = (algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p
            (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k *
          ((σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b) - b := by

  have hcoc : IsCoc p K.fixingSubgroup k c := hcocycle
  suffices h : ∃ b, c = cob p K.fixingSubgroup k b by
    obtain ⟨b, hb⟩ := h
    exact ⟨b, fun σ => congrFun hb σ⟩

  set H := (Kinf p K).fixingSubgroup with hH
  have hHG : H ≤ K.fixingSubgroup := fixingSubgroup_Kinf_le p K
  let ι : H → K.fixingSubgroup := fun τ => ⟨τ, hHG τ.2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  let cH : H → ℂ_[p] := fun τ => c (ι τ)
  have hΛH : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ H → Λ p k τ = 1 := fun τ hτ =>
    Λ_eq_one_of_χ p (χ_eq_one_of_forall p (mem_fixingSubgroup_F_of_mem_Kinf p K hτ))
  obtain ⟨b₀, hb₀⟩ :=
    PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower p K
      cH (hc.comp hι) (fun σ τ => by
        show c (ι σ * ι τ) = c (ι σ) + (σ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) • c (ι τ)
        rw [hcoc, show ((ι σ : K.fixingSubgroup) : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) = (σ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) from rfl, hΛH _ σ.2, one_mul])
  set c₁ : K.fixingSubgroup → ℂ_[p] := c - cob p K.fixingSubgroup k b₀ with hc₁
  have hcoc₁ : IsCoc p K.fixingSubgroup k c₁ := hcoc.sub (isCoc_cob b₀)
  have hcont₁ : Continuous c₁ := hc.sub (continuous_cob b₀)
  have hH₁ : ∀ τ : K.fixingSubgroup, (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) ∈ H → c₁ τ = 0 := by
    intro τ hτ
    have := hb₀ ⟨τ, hτ⟩
    change c τ = (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) • b₀ - b₀ at this
    simp only [hc₁, Pi.sub_apply, cob, hΛH _ hτ, one_mul]
    rw [this, sub_self]

  obtain ⟨d, hd, hR⟩ := exists_traces p
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, (p : ℝ) ^ (-(m₁ : ℤ)) * d < 1 := by
    obtain ⟨m₁, h⟩ := PadicInt.exists_pow_neg_lt p (show 0 < d⁻¹ from inv_pos.2 hd)
    refine ⟨m₁, ?_⟩
    calc (p : ℝ) ^ (-(m₁ : ℤ)) * d < d⁻¹ * d := mul_lt_mul_of_pos_right h hd
      _ = 1 := inv_mul_cancel₀ hd.ne'
  obtain ⟨m, hm, σ₀', hσ₀'G, hgen⟩ := exists_isGen_mem p K m₁
  set σ₀ : K.fixingSubgroup := ⟨σ₀', hσ₀'G⟩ with hσ₀
  obtain ⟨R, hRm⟩ := hR m

  set υ : ℚ_[p] := ((χ p σ₀' : ℤ_[p]) : ℚ_[p]) with hυ
  set μ : ℚ_[p] := υ ^ (-k) with hμ
  have hυ1 : ‖υ‖ = 1 := norm_coe_χ p σ₀'
  have hυ0 : υ ≠ 0 := coe_χ_ne_zero p σ₀'
  have hυpow : ∀ n : ℕ, 0 < n → υ ^ n ≠ 1 := by
    intro n hn h
    apply χ_zpow_ne_one hgen (k := (n : ℤ)) (by exact_mod_cast hn.ne')
    rw [zpow_natCast]
    apply Units.ext
    apply Subtype.val_injective
    change (((χ p σ₀' ^ n : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = (((1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
    rw [Units.val_pow_eq_pow_val, Units.val_one, PadicInt.coe_one, PadicInt.coe_pow]
    exact h
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [hμ] at h
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · rw [zpow_neg, zpow_natCast, inv_eq_one] at h
      exact hυpow n (by omega) h
    · rw [neg_neg, zpow_natCast] at h
      exact hυpow n (by omega) h
  have hμd : ‖μ - 1‖ * d < 1 := by
    have h1 : ‖μ - 1‖ ≤ (p : ℝ) ^ (-(m₁ : ℤ)) := by
      calc ‖μ - 1‖ ≤ ‖υ - 1‖ := norm_zpow_sub_one_le hυ1 (-k)
        _ ≤ (p : ℝ) ^ (-((m + 2 : ℕ) : ℤ)) := norm_χ_sub_one_le p hgen.1
        _ ≤ (p : ℝ) ^ (-(m₁ : ℤ)) := zpow_le_zpow_right₀ hp1 (by push_cast; omega)
    calc ‖μ - 1‖ * d ≤ (p : ℝ) ^ (-(m₁ : ℤ)) * d := mul_le_mul_of_nonneg_right h1 hd.le
      _ < 1 := hm₁
  have hΛμ : Λ p k σ₀' * algebraMap ℚ_[p] ℂ_[p] μ = 1 := by
    rw [Λ_eq, ← map_mul, ← hυ, hμ, ← zpow_add₀ hυ0, add_neg_cancel, zpow_zero, map_one]

  have hbij := PadicComplex.bijOn_towerClosure_smul_sub_mul_of_isTateTrace p (Fm p) (Fm_mono p)
    (fun n => inferInstance) m d R hRm σ₀' hgen.1 hgen.2
    (fun n y hy => gal_mem_F p σ₀' (n + 2) hy) μ hμ1 hμd

  obtain ⟨x, hxF, hx⟩ := exists_coords_of_mem_TK p K (apply_mem_TK_of_vanish hcoc₁ hH₁ σ₀)
  have hy : ∀ i, ∃ y ∈ (XF p : Set ℂ_[p]),
      σ₀' • y - algebraMap ℚ_[p] ℂ_[p] μ * y = algebraMap ℚ_[p] ℂ_[p] μ * x i := by
    intro i
    have hmem : algebraMap ℚ_[p] ℂ_[p] μ * x i ∈ PadicComplex.towerClosure p (Fm p) := by
      rw [← coe_XF]; exact Subfield.mul_mem _ (algebraMap_mem_XF p μ) (hxF i)
    obtain ⟨y, hy, hyx⟩ := hbij.surjOn hmem
    exact ⟨y, by rw [coe_XF]; exact hy, hyx⟩
  choose y hyF hyeq using hy
  set b : ℂ_[p] := ∑ i, eK p K i * y i with hb
  have hbH : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ H → τ • b = b := by
    intro τ hτ
    rw [hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_eK p K (hHG hτ)]
    congr 1
    have hyi : y i ∈ closure (Set.range fun k : Finf p => ((k : PadicAlgCl p) : ℂ_[p])) := by
      rw [← coe_XF']; exact hyF i
    exact (PadicComplex.forall_smul_eq_self_iff_mem_closure p (Finf p) (y i)).2 hyi τ
      (mem_fixingSubgroup_Finf_of_mem_Kinf p K hτ)
  have hbσ₀ : c₁ σ₀ = cob p K.fixingSubgroup k b σ₀ := by
    simp only [cob]
    rw [show ((σ₀ : K.fixingSubgroup) : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) = σ₀' from rfl, hx, hb, Finset.smul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_eK p K hσ₀'G]
    have := hyeq i
    linear_combination (-(Λ p k σ₀' * eK p K i)) * this - (eK p K i * x i + eK p K i * y i) * hΛμ
  set c₂ : K.fixingSubgroup → ℂ_[p] := c₁ - cob p K.fixingSubgroup k b with hc₂
  have hcoc₂ : IsCoc p K.fixingSubgroup k c₂ := hcoc₁.sub (isCoc_cob b)
  have hcont₂ : Continuous c₂ := hcont₁.sub (continuous_cob b)
  have hH₂ : ∀ τ : K.fixingSubgroup, (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) ∈ H → c₂ τ = 0 := by
    intro τ hτ
    simp only [hc₂, Pi.sub_apply, hH₁ τ hτ, cob, hΛH _ hτ, hbH _ hτ, one_mul, sub_self]
  have h0₂ : c₂ σ₀ = 0 := by
    simp only [hc₂, Pi.sub_apply, hbσ₀, sub_self]

  have hH₂' : ∀ τ : K.fixingSubgroup, (∀ n, (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) ∈ (F p n).fixingSubgroup) → c₂ τ = 0 := by
    intro τ hτ
    refine hH₂ τ ?_
    rw [hH, Kinf, IntermediateField.fixingSubgroup_sup]
    refine ⟨τ.2, ?_⟩
    have : Finf p ≤ IntermediateField.fixedField (Subgroup.zpowers (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))) :=
      iSup_le fun n => (IntermediateField.le_iff_le _ _).2
        ((Subgroup.zpowers_le (G := (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))).2 (hτ n))
    exact (Subgroup.zpowers_le (G := (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))).1 ((IntermediateField.le_iff_le _ _).1 this)
  have hN₂ : ∀ τ : K.fixingSubgroup, (τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) ∈ (Fm p m).fixingSubgroup → c₂ τ = 0 :=
    vanish_of_gen hcoc₂ hcont₂ hH₂' hgen h0₂
  set N : Subgroup K.fixingSubgroup := ((Fm p m).fixingSubgroup).subgroupOf K.fixingSubgroup with hN
  haveI : N.FiniteIndex := by
    refine ⟨fun h0 => ?_⟩
    have h1 : ((Fm p m).fixingSubgroup ⊓ K.fixingSubgroup).relIndex K.fixingSubgroup *
        K.fixingSubgroup.index = ((Fm p m).fixingSubgroup ⊓ K.fixingSubgroup).index :=
      Subgroup.relIndex_mul_index inf_le_right
    rw [Subgroup.inf_relIndex_right] at h1
    change N.index * K.fixingSubgroup.index = _ at h1
    rw [h0, zero_mul, ← IntermediateField.fixingSubgroup_sup,
      ← IntermediateField.finrank_eq_fixingSubgroup_index] at h1
    haveI : FiniteDimensional ℚ_[p] (Fm p m ⊔ K : IntermediateField ℚ_[p] (PadicAlgCl p)) :=
      IntermediateField.finiteDimensional_sup _ _
    exact Module.finrank_pos.ne' h1.symm
  obtain ⟨b', hb'⟩ := exists_eq_cob_of_vanish hcoc₂ N (fun τ hτ => hN₂ τ hτ)
  refine ⟨b₀ + b + b', ?_⟩
  rw [cob_add, cob_add, ← hb', hc₂, hc₁]
  abel

end
p2m_reactivate "P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2.XF P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.TT2"

end S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle
end P2MW
export P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle (solution)
