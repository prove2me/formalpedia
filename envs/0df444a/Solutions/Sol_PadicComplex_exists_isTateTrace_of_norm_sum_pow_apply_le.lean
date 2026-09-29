-- Prove2me | solution 1 for PadicComplex.exists_isTateTrace_of_norm_sum_pow_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2ed6c0b6-4cbf-59bc-90ff-46501fb6fe3e

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le

set_option autoImplicit false

noncomputable section

namespace TNT

open UniformSpace
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section A

variable (p)
variable (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p))

def IsGen (n : ℕ) (σ : Γ) : Prop := σ ∈ (Km n).fixingSubgroup ∧ σ ∉ (Km (n + 1)).fixingSubgroup

variable {Km}

lemma apply_eq_of_mem_fixingSubgroup {n : ℕ} {σ : Γ} (hσ : σ ∈ (Km n).fixingSubgroup) {y : Ω}
    (hy : y ∈ Km n) : σ y = y :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ y hy

lemma pow_apply_eq_of_mem_fixingSubgroup {n : ℕ} {σ : Γ} (hσ : σ ∈ (Km n).fixingSubgroup)
    (i : ℕ) {y : Ω} (hy : y ∈ Km n) : (σ ^ i) y = y :=
  apply_eq_of_mem_fixingSubgroup p (Subgroup.pow_mem _ hσ i) hy

variable (hmono : Monotone Km)
  (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup →
      σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)

include hcyc in
lemma isGen_pow (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (k : ℕ) :
    IsGen p Km (n + k) (σ ^ (p ^ k)) := by
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
      have h := hcyc (n + k) _ ih.1 ih.2
      refine ⟨?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h.1
      · rw [pow_succ, pow_mul]
        have : n + (k + 1) + 1 = n + k + 2 := by ring
        rw [this]; exact h.2

include hcyc in

lemma pow_mem_fixingSubgroup_succ_iff (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (i : ℕ) :
    σ ^ i ∈ (Km (n + 1)).fixingSubgroup ↔ p ∣ i := by
  constructor
  · intro hi
    by_contra hpi
    have hcop : Nat.Coprime i p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpi))

    obtain ⟨a, ha⟩ : ∃ a : ℕ, i * a % p = 1 := by
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp1
      exact ⟨a, ha⟩
    have hdiv : a * i = p * (a * i / p) + 1 := by
      have := Nat.div_add_mod (a * i) p
      rw [mul_comm] at ha
      omega
    apply hσ.2
    have h1 : σ ^ (a * i) ∈ (Km (n + 1)).fixingSubgroup := by
      rw [mul_comm, pow_mul]; exact Subgroup.pow_mem _ hi a
    have h2 : σ ^ (p * (a * i / p)) ∈ (Km (n + 1)).fixingSubgroup := by
      rw [pow_mul]; exact Subgroup.pow_mem _ (hcyc n σ hσ.1 hσ.2).1 _
    rw [hdiv, pow_add, pow_one] at h1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    simpa using this
  · rintro ⟨k, rfl⟩
    rw [pow_mul]
    exact Subgroup.pow_mem _ (hcyc n σ hσ.1 hσ.2).1 k

lemma sum_range_add_of_periodic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (P : ℕ)
    (hf : ∀ i, f (i + P) = f i) (j : ℕ) :
    ∑ i ∈ Finset.range P, f (i + j) = ∑ i ∈ Finset.range P, f i := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : ∑ i ∈ Finset.range P, f (i + (j + 1)) = ∑ i ∈ Finset.range P, f (i + 1 + j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; ring
      rw [h1]

      set g : ℕ → M := fun i => f (i + j) with hg
      have hgp : ∀ i, g (i + P) = g i := fun i => by
        simp only [hg]
        rw [show i + P + j = i + j + P by ring, hf]
      have h2 : ∑ i ∈ Finset.range P, f (i + 1 + j) = ∑ i ∈ Finset.range P, g (i + 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hg]
      rw [h2, ← ih]
      show ∑ i ∈ Finset.range P, g (i + 1) = ∑ i ∈ Finset.range P, g i
      rcases Nat.eq_zero_or_pos P with hP | hP
      · subst hP; simp
      · obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ' g]
        have h0 := hgp 0
        rw [zero_add] at h0
        rw [h0]

lemma norm_algEquiv (σ : Γ) (z : Ω) : ‖σ z‖ = ‖z‖ :=
  (spectralNorm_eq_of_equiv σ z).symm

lemma norm_algEquiv_sub (σ : Γ) (z w : Ω) : ‖σ z - σ w‖ = ‖z - w‖ := by
  rw [← map_sub, norm_algEquiv]

lemma norm_pow_apply_sub_le (σ : Γ) (z : Ω) (N : ℕ) : ‖(σ ^ N) z - z‖ ≤ ‖σ z - z‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hrw : (σ ^ (N + 1)) z - z = (σ ((σ ^ N) z) - σ z) + (σ z - z) := by
        rw [pow_succ', AlgEquiv.mul_apply]; abel
      rw [hrw]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
      rw [norm_algEquiv_sub]; exact ih

variable (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
  (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
  (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
    ∀ y ∈ Km m, σ y ∈ Km m)

lemma index_eq (n : ℕ) : (Km n).fixingSubgroup.index = Module.finrank ℚ_[p] (Km n) :=
  (IntermediateField.finrank_eq_fixingSubgroup_index _ (Km n)).symm

include hfin in
lemma index_ne_zero (n : ℕ) : (Km n).fixingSubgroup.index ≠ 0 := by
  haveI := hfin n
  rw [index_eq p]
  exact Module.finrank_pos.ne'

include hfin hdeg hmono in
lemma relIndex_eq (n : ℕ) :
    (Km (n + 1)).fixingSubgroup.relIndex (Km n).fixingSubgroup = p := by
  have hle : (Km (n + 1)).fixingSubgroup ≤ (Km n).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (hmono (Nat.le_succ n))
  have h := Subgroup.relIndex_mul_index hle
  rw [index_eq p, index_eq p, hdeg n (n + 1) rfl] at h
  have hpos : Module.finrank ℚ_[p] (Km n) ≠ 0 := by
    haveI := hfin n
    exact Module.finrank_pos.ne'
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) h

include hfin hdeg hmono in

lemma exists_isGen (n : ℕ) : ∃ σ : Γ, IsGen p Km n σ := by
  have h := relIndex_eq p hmono hfin hdeg n
  have hne : ¬ (Km n).fixingSubgroup ≤ (Km (n + 1)).fixingSubgroup := by
    intro hle
    rw [← Subgroup.relIndex_eq_one] at hle
    rw [hle] at h
    exact (Fact.out : p.Prime).one_lt.ne h
  obtain ⟨σ, hσ, hσ'⟩ := SetLike.not_le_iff_exists.mp hne
  exact ⟨σ, hσ, hσ'⟩

include hcyc in
lemma zpow_mem_fixingSubgroup_succ_iff (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (z : ℤ) :
    σ ^ z ∈ (Km (n + 1)).fixingSubgroup ↔ (p : ℤ) ∣ z := by
  rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, pow_mem_fixingSubgroup_succ_iff p hcyc n σ hσ, Int.natCast_dvd_natCast]
  · rw [zpow_neg, zpow_natCast, inv_mem_iff, pow_mem_fixingSubgroup_succ_iff p hcyc n σ hσ,
      Int.dvd_neg, Int.natCast_dvd_natCast]

include hfin hdeg hmono hcyc in

lemma exists_pow_inv_mul_mem (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (τ : Γ)
    (hτ : τ ∈ (Km n).fixingSubgroup) :
    ∃ i : ℕ, i < p ∧ (σ ^ i)⁻¹ * τ ∈ (Km (n + 1)).fixingSubgroup := by
  classical
  set H : Subgroup Γ := (Km n).fixingSubgroup with hH
  set H' : Subgroup Γ := (Km (n + 1)).fixingSubgroup with hH'
  set Q := H ⧸ H'.subgroupOf H with hQ
  have hcard : Nat.card Q = p := by
    have := relIndex_eq p hmono hfin hdeg n
    exact this
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
    rw [h3, zpow_mem_fixingSubgroup_succ_iff p hcyc n σ hσ] at h1
    have h4 : ((j : ℤ) - (i : ℤ)) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h1
      have hi := i.2; have hj := j.2
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)
  have hbij := hf.bijective_of_nat_card_le (by simp [hcard])
  obtain ⟨i, hi⟩ := hbij.2 (QuotientGroup.mk ⟨τ, hτ⟩)
  refine ⟨i, i.2, ?_⟩
  have h1 : (s ^ (i : ℕ))⁻¹ * ⟨τ, hτ⟩ ∈ H'.subgroupOf H := QuotientGroup.eq.mp hi
  rw [Subgroup.mem_subgroupOf] at h1
  simpa [s] using h1

include hfin hdeg hmono hcyc in

lemma exists_forall_apply_eq_pow_apply (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) :
    ∃ j : ℕ, ∀ y ∈ Km (m + k), τ y = (σ ^ j) y := by
  induction k with
  | zero =>
      refine ⟨0, fun y hy => ?_⟩
      rw [pow_zero, AlgEquiv.one_apply]
      exact apply_eq_of_mem_fixingSubgroup p (by simpa using hτ) hy
  | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      set ρ : Γ := (σ ^ j)⁻¹ * τ with hρ
      have hρm : ρ ∈ (Km (m + k)).fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        rw [hρ, AlgEquiv.mul_apply, hj y hy, ← AlgEquiv.mul_apply, inv_mul_cancel,
          AlgEquiv.one_apply]
      have hgen := isGen_pow p hcyc m σ hσ k
      obtain ⟨i, -, hi⟩ := exists_pow_inv_mul_mem p hmono hcyc hfin hdeg (m + k) _ hgen ρ hρm
      refine ⟨j + p ^ k * i, fun y hy => ?_⟩
      set ρ' : Γ := ((σ ^ p ^ k) ^ i)⁻¹ * ρ with hρ'
      have hτeq : τ = σ ^ j * ((σ ^ p ^ k) ^ i * ρ') := by
        rw [hρ', mul_inv_cancel_left, hρ, mul_inv_cancel_left]
      have hy' : ρ' y = y := apply_eq_of_mem_fixingSubgroup p hi (by
        have : m + (k + 1) = m + k + 1 := by ring
        rwa [this] at hy)
      rw [hτeq, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', ← pow_mul, ← AlgEquiv.mul_apply,
        ← pow_add]

include hfin hdeg hmono hcyc hstab in

lemma apply_comm (m n : ℕ) (hmn : m ≤ n) (τ τ' : Γ) (hτ : τ ∈ (Km m).fixingSubgroup)
    (hτ' : τ' ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km n) : τ (τ' y) = τ' (τ y) := by
  obtain ⟨σ, hσ⟩ := exists_isGen p hmono hfin hdeg m
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨j, hj⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ hτ
  obtain ⟨j', hj'⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ' hτ'
  have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (hmono (Nat.zero_le m))
  have hσ0 : σ ∈ (Km 0).fixingSubgroup := h0 hσ.1
  have hy1 : (σ ^ j') y ∈ Km (m + k) := hstab _ _ (Subgroup.pow_mem _ hσ0 _) y hy
  have hy2 : (σ ^ j) y ∈ Km (m + k) := hstab _ _ (Subgroup.pow_mem _ hσ0 _) y hy
  rw [hj' y hy, hj _ hy1, hj y hy, hj' _ hy2, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply,
    ← pow_add, ← pow_add, add_comm]

include hfin hdeg hmono hcyc in

lemma norm_apply_sub_le_of_isGen (m n : ℕ) (hmn : m ≤ n) (σ : Γ) (hσ : IsGen p Km m σ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) (z : Ω) (hz : z ∈ Km n) : ‖τ z - z‖ ≤ ‖σ z - z‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨j, hj⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ hτ
  rw [hj z hz]
  exact norm_pow_apply_sub_le p σ z j

include hfin hdeg hmono hcyc hstab in

lemma sum_pow_apply_mem (n : ℕ) (σ : Γ) (hσ : IsGen p Km n σ) (y : Ω) (hy : y ∈ Km (n + 1)) :
    ∑ i ∈ Finset.range p, (σ ^ i) y ∈ Km n := by
  have hfix : ∀ ρ ∈ (Km n).fixingSubgroup, ρ (∑ i ∈ Finset.range p, (σ ^ i) y) =
      ∑ i ∈ Finset.range p, (σ ^ i) y := by
    intro ρ hρ
    obtain ⟨j, hj⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg n σ hσ 1 ρ hρ
    have h0 : (Km n).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (hmono (Nat.zero_le n))
    have hσ0 : σ ∈ (Km 0).fixingSubgroup := h0 hσ.1
    rw [map_sum]
    have h1 : ∀ i ∈ Finset.range p, ρ ((σ ^ i) y) = (σ ^ (i + j)) y := by
      intro i _
      rw [hj _ (hstab _ _ (Subgroup.pow_mem _ hσ0 _) y hy), ← AlgEquiv.mul_apply, ← pow_add,
        add_comm]
    rw [Finset.sum_congr rfl h1]
    apply sum_range_add_of_periodic (fun i => (σ ^ i) y) p
    intro i
    show (σ ^ (i + p)) y = (σ ^ i) y
    rw [pow_add, AlgEquiv.mul_apply, apply_eq_of_mem_fixingSubgroup p (hcyc n σ hσ.1 hσ.2).1 hy]
  have hmem : (∑ i ∈ Finset.range p, (σ ^ i) y) ∈
      IntermediateField.fixedField (Km n).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    exact hfix
  rwa [InfiniteGalois.fixedField_fixingSubgroup] at hmem

end A

section B

variable (p)
variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)}

def Ssum (σ : Γ) (k : ℕ) (y : Ω) : Ω := ∑ j ∈ Finset.range (p ^ k), (σ ^ j) y

def Nop (σ : Γ) (k : ℕ) (y : Ω) : Ω := ∑ a ∈ Finset.range p, ((σ ^ p ^ k) ^ a) y

def Top (σ : Γ) (k : ℕ) (y : Ω) : Ω := ((p : Ω) ^ k)⁻¹ * Ssum p σ k y

lemma natCast_p_ne_zero : (p : Ω) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma norm_natCast_p : ‖(p : Ω)‖ = ‖(p : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap']

lemma norm_p_pos : 0 < ‖(p : ℚ_[p])‖ := by
  rw [Padic.norm_p]; have := (Fact.out : p.Prime).pos; positivity

@[scoped simp] lemma Ssum_add (σ : Γ) (k : ℕ) (y y' : Ω) :
    Ssum p σ k (y + y') = Ssum p σ k y + Ssum p σ k y' := by
  simp [Ssum, Finset.sum_add_distrib]

@[scoped simp] lemma Ssum_sub (σ : Γ) (k : ℕ) (y y' : Ω) :
    Ssum p σ k (y - y') = Ssum p σ k y - Ssum p σ k y' := by
  simp [Ssum, Finset.sum_sub_distrib]

@[scoped simp] lemma Nop_add (σ : Γ) (k : ℕ) (y y' : Ω) :
    Nop p σ k (y + y') = Nop p σ k y + Nop p σ k y' := by
  simp only [Nop, map_add, Finset.sum_add_distrib]

@[scoped simp] lemma Nop_sub (σ : Γ) (k : ℕ) (y y' : Ω) :
    Nop p σ k (y - y') = Nop p σ k y - Nop p σ k y' := by
  simp only [Nop, map_sub, Finset.sum_sub_distrib]

lemma pow_apply_of_apply_eq (σ : Γ) {a : Ω} (ha : σ a = a) (j : ℕ) : (σ ^ j) a = a := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]

lemma Ssum_mul_of_fixed (σ : Γ) (k : ℕ) (a y : Ω) (ha : σ a = a) :
    Ssum p σ k (a * y) = a * Ssum p σ k y := by
  simp only [Ssum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_apply_of_apply_eq p σ ha j]

lemma Top_add (σ : Γ) (k : ℕ) (y y' : Ω) : Top p σ k (y + y') = Top p σ k y + Top p σ k y' := by
  simp [Top, mul_add]

lemma Top_mul_of_fixed (σ : Γ) (k : ℕ) (a y : Ω) (ha : σ a = a) :
    Top p σ k (a * y) = a * Top p σ k y := by
  simp only [Top, Ssum_mul_of_fixed p σ k a y ha]; ring

lemma sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n c : ℕ) :
    ∑ j ∈ Finset.range (n * c), f j = ∑ a ∈ Finset.range c, ∑ b ∈ Finset.range n, f (n * a + b) := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma Ssum_succ (σ : Γ) (k : ℕ) (y : Ω) : Ssum p σ (k + 1) y = Ssum p σ k (Nop p σ k y) := by
  simp only [Ssum, Nop]
  rw [pow_succ, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add, add_comm]

lemma Top_succ (σ : Γ) (k : ℕ) (y : Ω) :
    Top p σ (k + 1) y = Top p σ k ((p : Ω)⁻¹ * Nop p σ k y) := by
  have hp : σ ((p : Ω)⁻¹) = (p : Ω)⁻¹ := by rw [map_inv₀, map_natCast]
  rw [Top_mul_of_fixed p σ k _ _ hp]
  simp only [Top, Ssum_succ]
  rw [pow_succ]
  field_simp

variable (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup →
      σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)
  (hmono : Monotone Km)
  (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
  (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
  (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
    ∀ y ∈ Km m, σ y ∈ Km m)

include hcyc in

lemma Nop_eq_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω) (hy : y ∈ Km (m + k)) :
    Nop p σ k y = (p : Ω) * y := by
  have hgen := isGen_pow p hcyc m σ hσ k
  simp only [Nop]
  rw [Finset.sum_congr rfl fun a _ => pow_apply_eq_of_mem_fixingSubgroup p hgen.1 a hy]
  simp

include hcyc in

lemma Top_succ_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω)
    (hy : y ∈ Km (m + k)) : Top p σ (k + 1) y = Top p σ k y := by
  rw [Top_succ, Nop_eq_of_mem p hcyc m σ hσ k y hy, ← mul_assoc, inv_mul_cancel₀ (natCast_p_ne_zero p),
    one_mul]

include hcyc hmono in
lemma Top_eq_of_le (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k k' : ℕ) (hk : k ≤ k') (y : Ω)
    (hy : y ∈ Km (m + k)) : Top p σ k' y = Top p σ k y := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction l with
  | zero => rfl
  | succ l ih =>
      rw [← add_assoc, Top_succ_of_mem p hcyc m σ hσ (k + l) y (hmono (by omega) hy)]
      exact ih (by omega)

lemma Top_eq_self (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω) (hy : y ∈ Km m) :
    Top p σ k y = y := by
  simp only [Top, Ssum]
  rw [Finset.sum_congr rfl fun j _ => pow_apply_eq_of_mem_fixingSubgroup p hσ.1 j hy]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (natCast_p_ne_zero p)), one_mul]

include hcyc hmono hfin hdeg hstab in

lemma Nop_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (y : Ω) (hy : y ∈ Km (m + k + 1)) :
    Nop p σ k y ∈ Km (m + k) := by
  unfold Nop
  exact sum_pow_apply_mem p hmono hcyc hfin hdeg hstab (m + k) _ (isGen_pow p hcyc m σ hσ k) y hy

include hcyc hmono hfin hdeg hstab in

lemma Top_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) :
    ∀ y ∈ Km (m + k), Top p σ k y ∈ Km m := by
  induction k with
  | zero =>
      intro y hy
      rw [Nat.add_zero] at hy
      rw [Top_eq_self p m σ hσ 0 y hy]; exact hy
  | succ k ih =>
      intro y hy
      rw [Top_succ]
      apply ih
      refine mul_mem (inv_mem (natCast_mem _ p)) ?_
      have hy' : y ∈ Km (m + k + 1) := by
        have : m + (k + 1) = m + k + 1 := by ring
        rwa [this] at hy
      exact Nop_mem p hcyc hmono hfin hdeg hstab m σ hσ k y hy'

include hcyc hmono hfin hdeg in

lemma Ssum_apply_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km (m + k)) :
    Ssum p σ k (τ y) = Ssum p σ k y := by
  obtain ⟨j₀, hj₀⟩ := exists_forall_apply_eq_pow_apply p hmono hcyc hfin hdeg m σ hσ k τ hτ
  simp only [Ssum]
  rw [hj₀ y hy]
  have h1 : ∀ j ∈ Finset.range (p ^ k), (σ ^ j) ((σ ^ j₀) y) = (σ ^ (j + j₀)) y := by
    intro j _; rw [← AlgEquiv.mul_apply, ← pow_add]
  rw [Finset.sum_congr rfl h1]
  apply sum_range_add_of_periodic (fun j => (σ ^ j) y) (p ^ k)
  intro j
  show (σ ^ (j + p ^ k)) y = (σ ^ j) y
  rw [pow_add, AlgEquiv.mul_apply,
    apply_eq_of_mem_fixingSubgroup p (isGen_pow p hcyc m σ hσ k).1 hy]

include hcyc hmono hfin hdeg in
lemma Top_apply_of_mem (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (k : ℕ) (τ : Γ)
    (hτ : τ ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km (m + k)) :
    Top p σ k (τ y) = Top p σ k y := by
  simp only [Top, Ssum_apply_of_mem p hcyc hmono hfin hdeg m σ hσ k τ hτ y hy]

lemma norm_p_mul_sub_Nop_le (σ : Γ) (k : ℕ) (z : Ω) :
    ‖(p : Ω) * z - Nop p σ k z‖ ≤ ‖(σ ^ p ^ k) z - z‖ := by
  have hrw : (p : Ω) * z - Nop p σ k z = ∑ a ∈ Finset.range p, (z - ((σ ^ p ^ k) ^ a) z) := by
    simp only [Nop, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrw]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun a _ => ?_
  rw [← norm_neg, neg_sub]
  exact norm_pow_apply_sub_le p _ z a

lemma norm_sub_inv_p_mul_Nop_le (σ : Γ) (k : ℕ) (z : Ω) :
    ‖z - (p : Ω)⁻¹ * Nop p σ k z‖ ≤ ‖(p : ℚ_[p])‖⁻¹ * ‖(σ ^ p ^ k) z - z‖ := by
  have hrw : z - (p : Ω)⁻¹ * Nop p σ k z = (p : Ω)⁻¹ * ((p : Ω) * z - Nop p σ k z) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (natCast_p_ne_zero p), one_mul]
  rw [hrw, norm_mul, norm_inv, norm_natCast_p]
  exact mul_le_mul_of_nonneg_left (norm_p_mul_sub_Nop_le p σ k z) (by positivity)

variable (c : ℕ → ℝ) (C : ℝ) (hc : ∀ m, 1 ≤ c m) (hC : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C)
  (htr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
      ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖)

def D (m k : ℕ) : ℝ := ‖(p : ℚ_[p])‖⁻¹ * ∏ j ∈ Finset.range k, c (m + j)

include hc in
lemma one_le_prod_c (m k : ℕ) : 1 ≤ ∏ j ∈ Finset.range k, c (m + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ]
      nlinarith [hc (m + k)]

include hc in
lemma D_nonneg (m k : ℕ) : 0 ≤ D p c m k := by
  unfold D
  have := one_le_prod_c c hc m k
  have := norm_p_pos (p := p)
  positivity

include hc in
lemma inv_norm_p_le_D (m k : ℕ) : ‖(p : ℚ_[p])‖⁻¹ ≤ D p c m k := by
  unfold D
  have h1 := one_le_prod_c c hc m k
  have h2 : 0 < ‖(p : ℚ_[p])‖⁻¹ := by have := norm_p_pos (p := p); positivity
  nlinarith

lemma D_succ (m k : ℕ) : D p c m (k + 1) = D p c m k * c (m + k) := by
  unfold D; rw [Finset.prod_range_succ]; ring

include hc hC in

lemma D_le (m k : ℕ) : D p c m k ≤ ‖(p : ℚ_[p])‖⁻¹ * C := by
  unfold D
  refine mul_le_mul_of_nonneg_left ?_ (by have := norm_p_pos (p := p); positivity)
  refine le_trans ?_ (hC (m + k))
  rw [Finset.prod_range_add]
  have h1 := one_le_prod_c c hc 0 m
  simp only [zero_add] at h1
  have h2 : 0 ≤ ∏ j ∈ Finset.range k, c (m + j) := zero_le_one.trans (one_le_prod_c c hc m k)
  nlinarith

include hcyc hmono hfin hdeg hstab hc htr in

lemma norm_sub_Top_le (m : ℕ) (σ : Γ) (hσ : IsGen p Km m σ) (σ' : Γ) (hσ' : IsGen p Km m σ')
    (k : ℕ) : ∀ y ∈ Km (m + k), ‖y - Top p σ k y‖ ≤ D p c m k * ‖σ' y - y‖ := by
  induction k with
  | zero =>
      intro y hy
      rw [Top_eq_self p m σ hσ 0 y (by simpa using hy), sub_self, norm_zero]
      exact mul_nonneg (D_nonneg p c hc m 0) (norm_nonneg _)
  | succ k ih =>
      intro y hy
      have hy' : y ∈ Km (m + k + 1) := by
        have : m + (k + 1) = m + k + 1 := by ring
        rwa [this] at hy
      have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
        IntermediateField.fixingSubgroup_le (hmono (Nat.zero_le m))
      have hgen := isGen_pow p hcyc m σ hσ k
      have hρm : σ ^ p ^ k ∈ (Km m).fixingSubgroup := Subgroup.pow_mem _ hσ.1 _

      have hNmem : Nop p σ k y ∈ Km (m + k) := Nop_mem p hcyc hmono hfin hdeg hstab m σ hσ k y hy'
      have hy₁mem : (p : Ω)⁻¹ * Nop p σ k y ∈ Km (m + k) :=
        mul_mem (inv_mem (natCast_mem _ p)) hNmem

      have hT : Top p σ (k + 1) y = Top p σ k ((p : Ω)⁻¹ * Nop p σ k y) := Top_succ p σ k y

      have h3 : ‖y - (p : Ω)⁻¹ * Nop p σ k y‖ ≤ ‖(p : ℚ_[p])‖⁻¹ * ‖σ' y - y‖ := by
        refine (norm_sub_inv_p_mul_Nop_le p σ k y).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by have := norm_p_pos (p := p); positivity)
        exact norm_apply_sub_le_of_isGen p hmono hcyc hfin hdeg m (m + k + 1) (by omega) σ' hσ'
          (σ ^ p ^ k) hρm y hy'

      have h4 : ‖σ' ((p : Ω)⁻¹ * Nop p σ k y) - (p : Ω)⁻¹ * Nop p σ k y‖ ≤
          c (m + k) * ‖σ' y - y‖ := by
        have hcomm : σ' (Nop p σ k y) = Nop p σ k (σ' y) := by
          unfold Nop
          rw [map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact apply_comm p hmono hcyc hfin hdeg hstab m (m + k + 1) (by omega) σ' ((σ ^ p ^ k) ^ a)
            hσ'.1 (Subgroup.pow_mem _ hρm a) y hy'
        have hrw : σ' ((p : Ω)⁻¹ * Nop p σ k y) - (p : Ω)⁻¹ * Nop p σ k y =
            (p : Ω)⁻¹ * Nop p σ k (σ' y - y) := by
          rw [map_mul, map_inv₀, map_natCast, hcomm, Nop_sub, mul_sub]
        rw [hrw, norm_mul, norm_inv, norm_natCast_p]
        have hw : σ' y - y ∈ Km (m + k + 1) := sub_mem (hstab _ _ (h0 hσ'.1) y hy') hy'
        have h5 := htr (m + k) (σ ^ p ^ k) hgen.1 hgen.2 (σ' y - y) hw
        have h5' : ‖Nop p σ k (σ' y - y)‖ ≤ ‖(p : ℚ_[p])‖ * c (m + k) * ‖σ' y - y‖ := by
          unfold Nop; exact h5
        have hp := norm_p_pos (p := p)
        calc ‖(p : ℚ_[p])‖⁻¹ * ‖Nop p σ k (σ' y - y)‖
            ≤ ‖(p : ℚ_[p])‖⁻¹ * (‖(p : ℚ_[p])‖ * c (m + k) * ‖σ' y - y‖) :=
              mul_le_mul_of_nonneg_left h5' (by positivity)
          _ = c (m + k) * ‖σ' y - y‖ := by field_simp

      have hsplit : y - Top p σ (k + 1) y = (y - (p : Ω)⁻¹ * Nop p σ k y) +
          ((p : Ω)⁻¹ * Nop p σ k y - Top p σ k ((p : Ω)⁻¹ * Nop p σ k y)) := by
        rw [hT]; abel
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact h3.trans (mul_le_mul_of_nonneg_right (inv_norm_p_le_D p c hc m (k + 1))
          (norm_nonneg _))
      · refine (ih _ hy₁mem).trans ?_
        rw [D_succ]
        have hD := D_nonneg p c hc m k
        calc D p c m k * ‖σ' ((p : Ω)⁻¹ * Nop p σ k y) - (p : Ω)⁻¹ * Nop p σ k y‖
              ≤ D p c m k * (c (m + k) * ‖σ' y - y‖) := mul_le_mul_of_nonneg_left h4 hD
          _ = D p c m k * c (m + k) * ‖σ' y - y‖ := by ring

end B

section C

variable (p)

structure Hyp (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (c : ℕ → ℝ) (C : ℝ) : Prop where
  mono : Monotone Km
  fin : ∀ m, FiniteDimensional ℚ_[p] (Km m)
  stab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
    ∀ y ∈ Km m, σ y ∈ Km m
  deg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m)
  cyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup →
      σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup
  one_le : ∀ m, 1 ≤ c m
  prod_le : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C
  tr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
      ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖

variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
variable (H : Hyp p Km c C)

def dconst (C : ℝ) : ℝ := ‖(p : ℚ_[p])‖⁻¹ * C

include H in
lemma one_le_C : 1 ≤ C := by simpa using H.prod_le 0

include H in
lemma dconst_pos : 0 < dconst p C := by
  unfold dconst
  have := one_le_C p H
  have := norm_p_pos (p := p)
  positivity

def gen (m : ℕ) : Γ := Classical.choose (exists_isGen p H.mono H.fin H.deg m)

lemma gen_spec (m : ℕ) : IsGen p Km m (gen p H m) :=
  Classical.choose_spec (exists_isGen p H.mono H.fin H.deg m)

open Classical in

def tΩ (m : ℕ) (y : Ω) : Ω :=
  if h : ∃ k, y ∈ Km (m + k) then Top p (gen p H m) (Classical.choose h) y else 0

include H in
lemma mem_add_of_mem {n : ℕ} (m : ℕ) {y : Ω} (hy : y ∈ Km n) : y ∈ Km (m + n) :=
  H.mono (Nat.le_add_left n m) hy

lemma unorm_sub_le_max (x y : Ω) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

lemma tΩ_eq (m k : ℕ) (y : Ω) (hy : y ∈ Km (m + k)) : tΩ p H m y = Top p (gen p H m) k y := by
  have h : ∃ k, y ∈ Km (m + k) := ⟨k, hy⟩
  unfold tΩ
  rw [dif_pos h]
  have hk₀ := Classical.choose_spec h
  rw [← Top_eq_of_le p H.cyc H.mono m _ (gen_spec p H m) _ (max k (Classical.choose h))
      (le_max_right _ _) y hk₀,
    Top_eq_of_le p H.cyc H.mono m _ (gen_spec p H m) k (max k (Classical.choose h))
      (le_max_left _ _) y hy]

lemma tΩ_add (m : ℕ) {n n' : ℕ} (y y' : Ω) (hy : y ∈ Km n) (hy' : y' ∈ Km n') :
    tΩ p H m (y + y') = tΩ p H m y + tΩ p H m y' := by
  have h1 : y ∈ Km (m + (n + n')) := H.mono (by omega) hy
  have h2 : y' ∈ Km (m + (n + n')) := H.mono (by omega) hy'
  rw [tΩ_eq p H m (n + n') y h1, tΩ_eq p H m (n + n') y' h2,
    tΩ_eq p H m (n + n') (y + y') (add_mem h1 h2), Top_add]

lemma tΩ_mul (m : ℕ) {n : ℕ} (a y : Ω) (ha : a ∈ Km m) (hy : y ∈ Km n) :
    tΩ p H m (a * y) = a * tΩ p H m y := by
  have h1 : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  have h2 : a * y ∈ Km (m + n) := mul_mem (H.mono (Nat.le_add_right m n) ha) h1
  rw [tΩ_eq p H m n _ h2, tΩ_eq p H m n y h1,
    Top_mul_of_fixed p _ n a y (apply_eq_of_mem_fixingSubgroup p (gen_spec p H m).1 ha)]

lemma tΩ_self (m : ℕ) (y : Ω) (hy : y ∈ Km m) : tΩ p H m y = y := by
  rw [tΩ_eq p H m 0 y (by simpa using hy), Top_eq_self p m _ (gen_spec p H m) 0 y hy]

lemma tΩ_mem (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) : tΩ p H m y ∈ Km m := by
  rw [tΩ_eq p H m n y (mem_add_of_mem p H m hy)]
  exact Top_mem p H.cyc H.mono H.fin H.deg H.stab m _ (gen_spec p H m) n y (mem_add_of_mem p H m hy)

lemma tΩ_apply (m : ℕ) {n : ℕ} (τ : Γ) (hτ : τ ∈ (Km m).fixingSubgroup) (y : Ω) (hy : y ∈ Km n) :
    tΩ p H m (τ y) = tΩ p H m y := by
  have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (H.mono (Nat.zero_le m))
  have h1 : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  have h2 : τ y ∈ Km (m + n) := H.stab _ _ (h0 hτ) y h1
  rw [tΩ_eq p H m n _ h2, tΩ_eq p H m n y h1,
    Top_apply_of_mem p H.cyc H.mono H.fin H.deg m _ (gen_spec p H m) n τ hτ y h1]

lemma norm_sub_tΩ_le (m : ℕ) (σ' : Γ) (hσ' : IsGen p Km m σ') {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    ‖y - tΩ p H m y‖ ≤ dconst p C * ‖σ' y - y‖ := by
  have h1 : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  rw [tΩ_eq p H m n y h1]
  refine (norm_sub_Top_le p H.cyc H.mono H.fin H.deg H.stab c H.one_le H.tr m _ (gen_spec p H m)
    σ' hσ' n y h1).trans ?_
  exact mul_le_mul_of_nonneg_right (D_le p c C H.one_le H.prod_le m n) (norm_nonneg _)

lemma norm_tΩ_le (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    ‖tΩ p H m y‖ ≤ max 1 (dconst p C) * ‖y‖ := by
  have h := norm_sub_tΩ_le p H m _ (gen_spec p H m) y hy
  have h1 : ‖gen p H m y - y‖ ≤ ‖y‖ := by
    refine (unorm_sub_le_max p _ _).trans ?_
    simp only [norm_algEquiv, max_self, le_refl]
  have hd := (dconst_pos p H).le
  have h2 : ‖y - tΩ p H m y‖ ≤ dconst p C * ‖y‖ := h.trans (mul_le_mul_of_nonneg_left h1 hd)
  have h3 : ‖tΩ p H m y‖ = ‖y - (y - tΩ p H m y)‖ := by congr 1; abel
  calc ‖tΩ p H m y‖ = ‖y - (y - tΩ p H m y)‖ := h3
    _ ≤ max ‖y‖ ‖y - tΩ p H m y‖ := unorm_sub_le_max p _ _
    _ ≤ max 1 (dconst p C) * ‖y‖ := by
        refine max_le ?_ ?_
        · calc ‖y‖ = 1 * ‖y‖ := (one_mul _).symm
            _ ≤ max 1 (dconst p C) * ‖y‖ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end C

section D

variable (p)
variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
variable (H : Hyp p Km c C)

def towerSubmodule : Submodule ℚ_[p] ℂ_[p] where
  carrier := ⋃ m : ℕ, Set.range fun k : Km m => ((k : Ω) : ℂ_[p])
  zero_mem' := Set.mem_iUnion.mpr ⟨0, ⟨0, by simp⟩⟩
  add_mem' := by
    intro u v hu hv
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    obtain ⟨n, ⟨l, rfl⟩⟩ := Set.mem_iUnion.mp hv
    refine Set.mem_iUnion.mpr ⟨max m n, ⟨⟨(k : Ω) + l, ?_⟩, ?_⟩⟩
    · exact add_mem (H.mono (le_max_left m n) k.2) (H.mono (le_max_right m n) l.2)
    · simp [Completion.coe_add]
  smul_mem' := by
    intro a u hu
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    refine Set.mem_iUnion.mpr ⟨m, ⟨⟨algebraMap ℚ_[p] Ω a * (k : Ω), ?_⟩, ?_⟩⟩
    · exact mul_mem (algebraMap_mem (Km m) a) k.2
    · simp only
      rw [Completion.coe_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p]]
      rfl

lemma mem_towerSubmodule_iff (z : ℂ_[p]) :
    z ∈ towerSubmodule p H ↔ ∃ n : ℕ, ∃ y : Ω, y ∈ Km n ∧ z = ((y : Ω) : ℂ_[p]) := by
  constructor
  · intro hz
    obtain ⟨n, ⟨k, hk⟩⟩ := Set.mem_iUnion.mp hz
    exact ⟨n, k, k.2, hk.symm⟩
  · rintro ⟨n, y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨⟨y, hy⟩, rfl⟩⟩

lemma coe_mem_towerSubmodule {n : ℕ} {y : Ω} (hy : y ∈ Km n) :
    ((y : Ω) : ℂ_[p]) ∈ towerSubmodule p H :=
  (mem_towerSubmodule_iff p H _).mpr ⟨n, y, hy, rfl⟩

lemma coe_topologicalClosure_towerSubmodule :
    ((towerSubmodule p H).topologicalClosure : Set ℂ_[p]) = PadicComplex.towerClosure p Km := by
  rw [Submodule.topologicalClosure_coe]; rfl

lemma mem_towerClosure_iff (z : ℂ_[p]) :
    z ∈ PadicComplex.towerClosure p Km ↔ z ∈ (towerSubmodule p H).topologicalClosure := by
  rw [← SetLike.mem_coe, coe_topologicalClosure_towerSubmodule]

def preim (z : ℂ_[p]) : Ω := Function.invFun ((↑) : Ω → ℂ_[p]) z

lemma preim_coe (y : Ω) : preim p ((y : Ω) : ℂ_[p]) = y :=
  Function.leftInverse_invFun (Completion.coe_injective (PadicAlgCl p)) y

def fS (m : ℕ) : towerSubmodule p H →ₗ[ℚ_[p]] ℂ_[p] where
  toFun z := ((tΩ p H m (preim p z.1) : Ω) : ℂ_[p])
  map_add' := by
    intro z z'
    obtain ⟨n, y, hy, hz⟩ := (mem_towerSubmodule_iff p H _).mp z.2
    obtain ⟨n', y', hy', hz'⟩ := (mem_towerSubmodule_iff p H _).mp z'.2
    simp only [Submodule.coe_add, hz, hz']
    rw [← Completion.coe_add, preim_coe, preim_coe, preim_coe, tΩ_add p H m y y' hy hy',
      Completion.coe_add]
  map_smul' := by
    intro a z
    obtain ⟨n, y, hy, hz⟩ := (mem_towerSubmodule_iff p H _).mp z.2
    simp only [Submodule.coe_smul, hz, RingHom.id_apply]
    rw [← Completion.coe_smul, preim_coe, preim_coe, Algebra.smul_def,
      tΩ_mul p H m _ y (algebraMap_mem (Km m) a) hy, ← Algebra.smul_def, Completion.coe_smul]

lemma fS_apply_coe (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    fS p H m ⟨((y : Ω) : ℂ_[p]), coe_mem_towerSubmodule p H hy⟩ = ((tΩ p H m y : Ω) : ℂ_[p]) := by
  simp [fS, preim_coe]

lemma norm_fS_le (m : ℕ) (z : towerSubmodule p H) :
    ‖fS p H m z‖ ≤ max 1 (dconst p C) * ‖z‖ := by
  obtain ⟨n, y, hy, hz⟩ := (mem_towerSubmodule_iff p H _).mp z.2
  have h1 : fS p H m z = ((tΩ p H m y : Ω) : ℂ_[p]) := by
    have : z = ⟨((y : Ω) : ℂ_[p]), coe_mem_towerSubmodule p H hy⟩ := Subtype.ext hz
    rw [this, fS_apply_coe p H m y hy]
  rw [h1, PadicComplex.norm_extends]
  have h2 : ‖z‖ = ‖y‖ := by
    rw [← PadicComplex.norm_extends p y, ← hz]; rfl
  rw [h2]
  exact norm_tΩ_le p H m y hy

def fSc (m : ℕ) : towerSubmodule p H →L[ℚ_[p]] ℂ_[p] :=
  (fS p H m).mkContinuous (max 1 (dconst p C)) (norm_fS_le p H m)

def incl : towerSubmodule p H →L[ℚ_[p]] (towerSubmodule p H).topologicalClosure :=
  { Submodule.inclusion (Submodule.le_topologicalClosure _) with
    cont := continuous_inclusion (Submodule.le_topologicalClosure _) }

lemma incl_apply (z : towerSubmodule p H) : (incl p H z : ℂ_[p]) = z := rfl

lemma denseRange_incl : DenseRange (incl p H) := by
  have : DenseRange (Set.inclusion
      (Submodule.le_topologicalClosure (towerSubmodule p H) : ((towerSubmodule p H) : Set ℂ_[p]) ⊆
        (towerSubmodule p H).topologicalClosure)) := by
    rw [denseRange_inclusion_iff]
    rw [Submodule.topologicalClosure_coe]
  exact this

lemma isUniformInducing_incl : IsUniformInducing (incl p H) := by
  have hiso : Isometry (incl p H) := Isometry.of_dist_eq fun _ _ => rfl
  exact hiso.isUniformInducing

def Fext (m : ℕ) : (towerSubmodule p H).topologicalClosure →L[ℚ_[p]] ℂ_[p] :=
  (fSc p H m).extend (incl p H)

lemma Fext_coe (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n)
    (h : ((y : Ω) : ℂ_[p]) ∈ (towerSubmodule p H).topologicalClosure) :
    Fext p H m ⟨((y : Ω) : ℂ_[p]), h⟩ = ((tΩ p H m y : Ω) : ℂ_[p]) := by
  have h1 : (⟨((y : Ω) : ℂ_[p]), h⟩ : (towerSubmodule p H).topologicalClosure) =
      incl p H ⟨((y : Ω) : ℂ_[p]), coe_mem_towerSubmodule p H hy⟩ := rfl
  rw [Fext, h1, ContinuousLinearMap.extend_eq _ (denseRange_incl p H) (isUniformInducing_incl p H)]
  show fS p H m _ = _
  exact fS_apply_coe p H m y hy

open Classical in

def R (m : ℕ) (z : ℂ_[p]) : ℂ_[p] :=
  if h : z ∈ (towerSubmodule p H).topologicalClosure then Fext p H m ⟨z, h⟩ else 0

lemma R_coe (m : ℕ) (w : (towerSubmodule p H).topologicalClosure) : R p H m (w : ℂ_[p]) = Fext p H m w := by
  unfold R; rw [dif_pos w.2]

lemma R_apply_coe (m : ℕ) {n : ℕ} (y : Ω) (hy : y ∈ Km n) :
    R p H m ((y : Ω) : ℂ_[p]) = ((tΩ p H m y : Ω) : ℂ_[p]) := by
  have h : ((y : Ω) : ℂ_[p]) ∈ (towerSubmodule p H).topologicalClosure :=
    Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)
  unfold R; rw [dif_pos h, Fext_coe p H m y hy h]

lemma closure_induction {P : (towerSubmodule p H).topologicalClosure → Prop}
    (hP : IsClosed {w | P w})
    (hS : ∀ (n : ℕ) (y : Ω) (hy : y ∈ Km n),
      P ⟨((y : Ω) : ℂ_[p]), Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)⟩)
    (w : (towerSubmodule p H).topologicalClosure) : P w := by
  refine (denseRange_incl p H).induction_on w hP fun s => ?_
  obtain ⟨n, y, hy, hs⟩ := (mem_towerSubmodule_iff p H _).mp s.2
  have : incl p H s = ⟨((y : Ω) : ℂ_[p]),
      Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)⟩ := Subtype.ext hs
  rw [this]
  exact hS n y hy

lemma coe_mul_mem_closure {n : ℕ} (k : Ω) (hk : k ∈ Km n) {z : ℂ_[p]}
    (hz : z ∈ (towerSubmodule p H).topologicalClosure) :
    ((k : Ω) : ℂ_[p]) * z ∈ (towerSubmodule p H).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hz ⊢
  refine map_mem_closure (continuous_const_mul _) hz fun w hw => ?_
  obtain ⟨n', y, hy, rfl⟩ := (mem_towerSubmodule_iff p H _).mp hw
  rw [← Completion.coe_mul]
  exact coe_mem_towerSubmodule p H
    (mul_mem (H.mono (le_max_left n n') hk) (H.mono (le_max_right n n') hy))

lemma smul_mem_closure (τ : Γ) (hτ : τ ∈ (Km 0).fixingSubgroup) {z : ℂ_[p]}
    (hz : z ∈ (towerSubmodule p H).topologicalClosure) :
    τ • z ∈ (towerSubmodule p H).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hz ⊢
  refine map_mem_closure (PadicComplex.continuous_smul_left p τ) hz fun w hw => ?_
  obtain ⟨n, y, hy, rfl⟩ := (mem_towerSubmodule_iff p H _).mp hw
  rw [PadicComplex.smul_coe]
  exact coe_mem_towerSubmodule p H (H.stab n τ hτ y hy)

include H in

lemma isClosed_range_coe (m : ℕ) :
    IsClosed (Set.range fun k : Km m => ((k : Ω) : ℂ_[p])) := by
  haveI := H.fin m
  let L : Km m →ₗ[ℚ_[p]] ℂ_[p] :=
    ((Algebra.linearMap Ω ℂ_[p]).restrictScalars ℚ_[p]).comp (Km m).val.toLinearMap
  have hrange : (Set.range fun k : Km m => ((k : Ω) : ℂ_[p])) = (LinearMap.range L : Set ℂ_[p]) := by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  rw [hrange]
  exact (LinearMap.range L).closed_of_finiteDimensional

theorem isTateTrace (m : ℕ) : PadicComplex.IsTateTrace p Km m (dconst p C) (R p H m) := by
  have hX := mem_towerClosure_iff p H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy
    rw [hX] at hx hy
    have hxy : x + y ∈ (towerSubmodule p H).topologicalClosure := add_mem hx hy
    unfold R
    rw [dif_pos hx, dif_pos hy, dif_pos hxy, ← map_add]
    rfl
  ·
    intro k x hx
    rw [hX] at hx
    let g : (towerSubmodule p H).topologicalClosure → (towerSubmodule p H).topologicalClosure :=
      fun w => ⟨((k : Ω) : ℂ_[p]) * w, coe_mul_mem_closure p H (k : Ω) k.2 w.2⟩
    have hg : Continuous g := (continuous_const.mul continuous_subtype_val).subtype_mk _
    have key : ∀ w : (towerSubmodule p H).topologicalClosure,
        Fext p H m (g w) = ((k : Ω) : ℂ_[p]) * Fext p H m w := by
      intro w
      apply closure_induction p H (P := fun w => Fext p H m (g w) = ((k : Ω) : ℂ_[p]) * Fext p H m w)
      · exact isClosed_eq ((Fext p H m).continuous.comp hg) (continuous_const.mul (Fext p H m).continuous)
      · intro n y hy
        have hky : (k : Ω) * y ∈ Km (m + n) :=
          mul_mem (H.mono (Nat.le_add_right m n) k.2) (H.mono (Nat.le_add_left n m) hy)
        have hg1 : g ⟨((y : Ω) : ℂ_[p]), Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)⟩ =
            ⟨(((k : Ω) * y : Ω) : ℂ_[p]),
              Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hky)⟩ := by
          apply Subtype.ext
          show ((k : Ω) : ℂ_[p]) * ((y : Ω) : ℂ_[p]) = (((k : Ω) * y : Ω) : ℂ_[p])
          rw [Completion.coe_mul]
        rw [hg1, Fext_coe p H m _ hky, Fext_coe p H m y hy, tΩ_mul p H m (k : Ω) y k.2 hy,
          Completion.coe_mul]
    have h1 := key ⟨x, hx⟩
    rw [R_coe p H m ⟨x, hx⟩]
    have : ((k : Ω) : ℂ_[p]) * x = ((g ⟨x, hx⟩ : (towerSubmodule p H).topologicalClosure) : ℂ_[p]) := rfl
    rw [this, R_coe, key]
  ·
    intro k
    rw [R_apply_coe p H m (k : Ω) k.2, tΩ_self p H m (k : Ω) k.2]
  ·
    intro x hx
    rw [hX] at hx
    have key : ∀ w : (towerSubmodule p H).topologicalClosure,
        Fext p H m w ∈ Set.range fun k : Km m => ((k : Ω) : ℂ_[p]) := by
      intro w
      apply closure_induction p H (P := fun w => Fext p H m w ∈ Set.range fun k : Km m => ((k : Ω) : ℂ_[p]))
      · exact (isClosed_range_coe p H m).preimage (Fext p H m).continuous
      · intro n y hy
        rw [Fext_coe p H m y hy]
        exact ⟨⟨tΩ p H m y, tΩ_mem p H m y hy⟩, rfl⟩
    obtain ⟨k, hk⟩ := key ⟨x, hx⟩
    refine ⟨k, ?_⟩
    rw [R_coe p H m ⟨x, hx⟩]
    exact hk.symm
  ·
    intro τ hτ x hx
    rw [hX] at hx
    have h0 : (Km m).fixingSubgroup ≤ (Km 0).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (H.mono (Nat.zero_le m))
    let g : (towerSubmodule p H).topologicalClosure → (towerSubmodule p H).topologicalClosure :=
      fun w => ⟨τ • (w : ℂ_[p]), smul_mem_closure p H τ (h0 hτ) w.2⟩
    have hg : Continuous g := ((PadicComplex.continuous_smul_left p τ).comp continuous_subtype_val).subtype_mk _
    have key : ∀ w : (towerSubmodule p H).topologicalClosure, Fext p H m (g w) = Fext p H m w := by
      intro w
      apply closure_induction p H (P := fun w => Fext p H m (g w) = Fext p H m w)
      · exact isClosed_eq ((Fext p H m).continuous.comp hg) (Fext p H m).continuous
      · intro n y hy
        have hτy : τ y ∈ Km n := H.stab n τ (h0 hτ) y hy
        have hg1 : g ⟨((y : Ω) : ℂ_[p]), Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hy)⟩ =
            ⟨((τ y : Ω) : ℂ_[p]),
              Submodule.le_topologicalClosure _ (coe_mem_towerSubmodule p H hτy)⟩ := by
          apply Subtype.ext
          show τ • ((y : Ω) : ℂ_[p]) = ((τ y : Ω) : ℂ_[p])
          rw [PadicComplex.smul_coe]
        rw [hg1, Fext_coe p H m _ hτy, Fext_coe p H m y hy, tΩ_apply p H m τ hτ y hy]
    have : τ • x = ((g ⟨x, hx⟩ : (towerSubmodule p H).topologicalClosure) : ℂ_[p]) := rfl
    rw [this, R_coe, key, ← R_coe p H m ⟨x, hx⟩]
  ·
    intro σ' hσ' hσ'' x hx
    rw [hX] at hx
    have hgen : IsGen p Km m σ' := ⟨hσ', hσ''⟩
    have key : ∀ w : (towerSubmodule p H).topologicalClosure,
        ‖(w : ℂ_[p]) - Fext p H m w‖ ≤ dconst p C * ‖σ' • (w : ℂ_[p]) - w‖ := by
      intro w
      apply closure_induction p H
        (P := fun w => ‖(w : ℂ_[p]) - Fext p H m w‖ ≤ dconst p C * ‖σ' • (w : ℂ_[p]) - w‖)
      · exact isClosed_le ((continuous_subtype_val.sub (Fext p H m).continuous).norm)
          (continuous_const.mul (((PadicComplex.continuous_smul_left p σ').comp
            continuous_subtype_val).sub continuous_subtype_val).norm)
      · intro n y hy
        show ‖((y : Ω) : ℂ_[p]) - Fext p H m _‖ ≤ dconst p C * ‖σ' • ((y : Ω) : ℂ_[p]) - (y : ℂ_[p])‖
        rw [Fext_coe p H m y hy, ← Completion.coe_sub, PadicComplex.norm_extends,
          PadicComplex.smul_coe, ← Completion.coe_sub, PadicComplex.norm_extends]
        exact norm_sub_tΩ_le p H m σ' hgen y hy
    have := key ⟨x, hx⟩
    rwa [← R_coe p H m ⟨x, hx⟩] at this

include H in

theorem main : ∃ d : ℝ, 0 < d ∧ ∀ m, ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R :=
  ⟨dconst p C, dconst_pos p H, fun m => ⟨R p H m, isTateTrace p H m⟩⟩

end D

end TNT
p2m_reactivate "P2MW.S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le.TNT"

end
p2m_reactivate "P2MW.S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le.TNT"

theorem solution
    (p : ℕ) [Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (hstab : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km 0).fixingSubgroup →
      ∀ y ∈ Km m, σ y ∈ Km m)
    (hdeg : ∀ m n : ℕ, n = m + 1 → Module.finrank ℚ_[p] (Km n) = p * Module.finrank ℚ_[p] (Km m))
    (hcyc : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
      σ ∉ (Km (m + 1)).fixingSubgroup →
        σ ^ p ∈ (Km (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (Km (m + 2)).fixingSubgroup)
    (c : ℕ → ℝ) (C : ℝ) (hc : ∀ m, 1 ≤ c m) (hC : ∀ n, ∏ m ∈ Finset.range n, c m ≤ C)
    (htr : ∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), σ ∈ (Km m).fixingSubgroup →
      σ ∉ (Km (m + 1)).fixingSubgroup → ∀ y ∈ Km (m + 1),
        ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c m * ‖y‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ m, ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R :=
  TNT.main p ⟨hmono, hfin, hstab, hdeg, hcyc, hc, hC, htr⟩

end S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le
end P2MW
export P2MW.S_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le (solution)
