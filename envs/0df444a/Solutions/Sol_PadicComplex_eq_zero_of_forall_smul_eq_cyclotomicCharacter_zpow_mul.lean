-- Prove2me | solution 1 for PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5862efc4-0546-59c9-bd6f-64093e49d41a

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
import Theorems.Thm_PadicComplex_exists_isTateTrace_cyclotomicTower
import Theorems.Thm_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul

set_option autoImplicit false

noncomputable section

namespace TH0

open scoped NNReal TensorProduct

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

section gen

variable (p)

abbrev Fm (m : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := F p (m + 2)

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

lemma χ_zpow_ne_one {m : ℕ} {σ : Γ} (hσ : IsGen p m σ) {z : ℤ} (hz : z ≠ 0) :
    (χ p σ) ^ z ≠ 1 := by
  have key : ∀ i : ℕ, 0 < i → χ p σ ^ i ≠ 1 := by
    intro i hi h
    obtain ⟨n, hn⟩ := exists_pow_not_mem hσ hi
    exact hn (mem_fixingSubgroup_F_of_χ_eq_one p (by rw [χ_pow, h]) (n + 2))
  rcases Int.eq_nat_or_neg z with ⟨i, rfl | rfl⟩
  · have hi : 0 < i := by omega
    rw [zpow_natCast]; exact key i hi
  · have hi : 0 < i := by omega
    rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]; exact key i hi

variable (p)

lemma exists_isGen (m₀ : ℕ) : ∃ m, m₀ ≤ m ∧ ∃ σ : Γ, IsGen p m σ := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j, (Fm p m₀).fixingSubgroup ≤ (Fm p (m₀ + j)).fixingSubgroup := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro τ hτ
        have h1 : τ ∈ (Fm p (m₀ + j)).fixingSubgroup := ih hτ
        by_contra h2
        exact hcon (m₀ + j) (by omega) τ ⟨h1, by rwa [show m₀ + (j + 1) = m₀ + j + 1 by ring] at h2⟩
  have hle : ∀ j, Fm p (m₀ + j) ≤ Fm p m₀ := by
    intro j
    have := (IntermediateField.le_iff_le _ _).2 (hstep j)
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at this
  have hfin : ∀ j, Module.finrank ℚ_[p] (Fm p (m₀ + j)) ≤ Module.finrank ℚ_[p] (Fm p m₀) := fun j =>
    IntermediateField.finrank_le_of_le_right (hle j)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set A := Module.finrank ℚ_[p] (Fm p m₀) with hA
  have h := hfin A
  rw [finrank_Fm] at h
  have h1 : p ^ (m₀ + A + 1) ≤ A := by
    calc p ^ (m₀ + A + 1) ≤ (p - 1) * p ^ (m₀ + A + 1) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ A := h
  have h2 : A < p ^ A := Nat.lt_pow_self hp1
  have h3 : p ^ A ≤ p ^ (m₀ + A + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end gen

section lgc

variable (p)

scoped instance neZero_prime_rat : NeZero ((p : ℕ) : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩

theorem cyclotomicCharacter_localGaloisToGlobal (σ : Γ) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv = χ p σ := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  set a := PadicInt.toZModPow n
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])
    with ha

  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have hζ : IsPrimitiveRoot (padicEmbedding p ζ₀) (p ^ n) :=
    hζ₀.map_of_injective (padicEmbedding p).toRingHom.injective
  have hσζ : σ (padicEmbedding p ζ₀) = (padicEmbedding p ζ₀) ^ a.val := by
    rw [← padicEmbedding_localGaloisToGlobal, ← map_pow]
    congr 1
    exact cyclotomicCharacter.spec p (localGaloisToGlobal p σ).toRingEquiv ζ₀ hζ₀.pow_eq_one
  unfold χ
  rw [cyclotomicCharacter.toZModPow]
  refine modularCyclotomicCharacter.unique (PadicAlgCl p)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (p ^ n))
    (σ : Ω ≃ₐ[ℚ_[p]] Ω).toRingEquiv (c := a) fun t ht => ?_
  have ht' : ((t : Ωˣ) : Ω) ^ (p ^ n) = 1 := by
    have := (mem_rootsOfUnity _ t).1 ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one ht'
  show σ ((t : Ωˣ) : Ω) = _
  rw [← hi, map_pow, hσζ, ← pow_mul, mul_comm, pow_mul]

end lgc

end TH0
p2m_reactivate "P2MW.S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul.TH0"

open TH0 in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv :
                ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 := by
  by_contra hc0

  let Kb : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥
  let χQ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℚ_[p]ˣ :=
    (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])).comp
      ((cyclotomicCharacter (PadicAlgCl p) p).comp
        (MonoidHom.mk' (fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p => σ.toRingEquiv) (fun _ _ => rfl)))
  have hχQ : ∀ σ, ((χQ σ : ℚ_[p]ˣ) : ℚ_[p]) = ((χ p σ : ℤ_[p]) : ℚ_[p]) := fun σ => rfl
  let ψ : Kb.fixingSubgroup →* ℚ_[p]ˣ := (zpowGroupHom k).comp (χQ.comp (Subgroup.subtype _))
  have hψ : ∀ σ : Kb.fixingSubgroup, ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) = ((χ p σ : ℤ_[p]) : ℚ_[p]) ^ k := by
    intro σ
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, zpowGroupHom_apply,
      Units.val_zpow_eq_zpow_val, hχQ]

  let x : TensorProduct ℚ_[p] ℂ_[p] ℚ_[p] := c ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])
  have hx : x ≠ 0 := by
    intro h
    apply hc0
    have h2 : (TensorProduct.rid ℚ_[p] ℂ_[p]) x = (TensorProduct.rid ℚ_[p] ℂ_[p]) 0 := by rw [h]
    rw [LinearEquiv.map_zero] at h2
    simpa [x] using h2
  have hxσ : ∀ σ : Kb.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] ℚ_[p]) x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : ℚ_[p]ˣ) : ℚ_[p])) * x := by
    intro σ
    simp only [x, Algebra.TensorProduct.map_tmul, PadicComplex.galAlgHom_apply, AlgHom.coe_id, id_eq,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [hc, cyclotomicCharacter_localGaloisToGlobal, hψ, ← map_zpow₀, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    simp [χ]

  obtain ⟨d, -, hR⟩ := PadicComplex.exists_isTateTrace_cyclotomicTower p
  have hψ' : ∀ σ : Kb.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Fm p m).fixingSubgroup) → ψ σ = 1 := by
    intro σ hσ
    have hall : ∀ n, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (F p n).fixingSubgroup := fun n =>
      IntermediateField.fixingSubgroup_le (F_mono p (Nat.le_add_right n 2)) (hσ n)
    have h1 : χ p σ = 1 := χ_eq_one_of_forall p hall
    apply Units.ext
    rw [hψ, h1, Units.val_one, Units.val_one, PadicInt.coe_one, one_zpow]
  obtain ⟨n, hn, hfin⟩ :=
    PadicComplex.exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul p Kb (Fm p) (Fm_mono p)
      (fun m => bot_le) (fun m => inferInstance) d 0 (fun m _ => hR m) ℚ_[p] ψ hψ' x hx hxσ

  obtain ⟨m, -, σ, hσ⟩ := exists_isGen p 0
  have hσb : σ ∈ Kb.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hy
    exact σ.commutes q
  have h := congrArg (fun u : ℚ_[p]ˣ => (u : ℚ_[p])) (hfin ⟨σ, hσb⟩)
  simp only [Units.val_pow_eq_pow_val, hψ, Units.val_one] at h
  rw [← zpow_natCast, ← zpow_mul] at h
  have hkn : k * (n : ℤ) ≠ 0 := mul_ne_zero hk (by exact_mod_cast hn.ne')
  apply χ_zpow_ne_one hσ hkn
  have hinjU : Function.Injective (Units.map (PadicInt.Coe.ringHom (p := p) : ℤ_[p] →* ℚ_[p])) := by
    intro u v huv
    apply Units.ext
    have h' := congrArg (fun w : ℚ_[p]ˣ => (w : ℚ_[p])) huv
    simp only [Units.coe_map] at h'
    exact Subtype.val_injective h'
  apply hinjU
  rw [map_zpow, map_one]
  apply Units.ext
  rw [Units.val_zpow_eq_zpow_val, Units.val_one]
  exact h

end
end S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
end P2MW
export P2MW.S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul (solution)
