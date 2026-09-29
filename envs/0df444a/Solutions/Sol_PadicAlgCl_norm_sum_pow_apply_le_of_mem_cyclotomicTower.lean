-- Prove2me | solution 1 for PadicAlgCl.norm_sum_pow_apply_le_of_mem_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3b31f707-5aae-5b28-9ecd-e3ada811f5eb

import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower

set_option autoImplicit false

noncomputable section

namespace CTR

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
local notation "L" => PadicAlgCl.cyclotomicTower p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

lemma natCast_p_ne_zero : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma rpow_p_injective : Function.Injective fun x : ℝ => (p : ℝ) ^ x :=
  (Real.strictMono_rpow_of_base_gt_one (one_lt_p p)).injective

private lemma _root_.CTR.exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ n) := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero ((p ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hne⟩
  haveI : IsCyclotomicExtension {p ^ n} Ω Ω := IsSepClosedOfCharZero.isCyclotomicExtension _ _
  exact IsCyclotomicExtension.exists_isPrimitiveRoot Ω Ω (S := {p ^ n}) rfl hne

p2m_export "CTR" "exists_isPrimitiveRoot"
lemma cyclotomicTower_eq_adjoin (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    L n = IntermediateField.adjoin ℚ_[p] {ζ} := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  apply le_antisymm
  · unfold PadicAlgCl.cyclotomicTower
    rw [IntermediateField.adjoin_le_iff]
    intro ξ (hξ : ξ ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · exact IntermediateField.adjoin.mono ℚ_[p] _ _ (Set.singleton_subset_iff.mpr hζ.pow_eq_one)

lemma mem_of_isPrimitiveRoot (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) : ζ ∈ L n :=
  PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p hζ.pow_eq_one

private lemma _root_.CTR.mem_fixingSubgroup_iff (n : ℕ) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : Γ) :
    σ ∈ (L n).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (mem_of_isPrimitiveRoot p n hζ)
  · intro h x hx
    rw [cyclotomicTower_eq_adjoin p n hζ] at hx
    have hle : IntermediateField.adjoin ℚ_[p] {ζ} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        IntermediateField.mem_fixedField_iff]
      intro f hf
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      have hnat : ∀ k : ℕ, (σ ^ k) ζ = ζ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
      · rw [zpow_natCast]; exact hnat k
      · rw [zpow_neg, zpow_natCast]
        have h1 := hnat k
        calc (σ ^ k)⁻¹ ζ = (σ ^ k)⁻¹ ((σ ^ k) ζ) := by rw [h1]
          _ = ζ := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hx' := hle hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.mem_zpowers σ)

p2m_export "CTR" "mem_fixingSubgroup_iff"
lemma pow_apply_eq_pow_pow (σ : Γ) {ζ : Ω} {a : ℕ} (h : σ ζ = ζ ^ a) (j : ℕ) :
    (σ ^ j) ζ = ζ ^ (a ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, map_pow, ih, ← pow_mul, ← pow_succ]

lemma mem_fixingSubgroup_iff_dvd {N n : ℕ} (hn : n ≤ N) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ N))
    (τ : Γ) {b : ℕ} (hb : 1 ≤ b) (hτ : τ ζ = ζ ^ b) :
    τ ∈ (L n).fixingSubgroup ↔ p ^ n ∣ b - 1 := by
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hζn : IsPrimitiveRoot (ζ ^ (p ^ (N - n))) (p ^ n) :=
    hζ.pow hpos (by rw [← pow_add, Nat.sub_add_cancel hn])
  rw [mem_fixingSubgroup_iff p n hζn, map_pow, hτ, ← pow_mul, mul_comm, pow_mul]
  set η : Ω := ζ ^ p ^ (N - n) with hη
  have hη0 : η ≠ 0 := hζn.ne_zero (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  have hsplit : η ^ b = η ^ (b - 1) * η := by rw [← pow_succ, Nat.sub_add_cancel hb]
  rw [hsplit]
  constructor
  · intro h
    have h1 : η ^ (b - 1) = 1 := by
      have h2 : η ^ (b - 1) * η = 1 * η := by rw [one_mul]; exact h
      exact mul_right_cancel₀ hη0 h2
    exact (hζn.pow_eq_one_iff_dvd _).mp h1
  · intro h
    rw [(hζn.pow_eq_one_iff_dvd _).mpr h, one_mul]

lemma norm_eq_one_of_pow_eq_one {ζ : Ω} {k : ℕ} (h : ζ ^ k = 1) (hk : k ≠ 0) : ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ k = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).mp h1

lemma norm_one_sub_pow_le {ζ : Ω} {N : ℕ} (hζ : ζ ^ N = 1) (hN : N ≠ 0) (a : ℕ) :
    ‖1 - ζ ^ a‖ ≤ ‖1 - ζ‖ := by
  have h1 : 1 - ζ ^ a = (∑ i ∈ Finset.range a, ζ ^ i) * (1 - ζ) := by
    have := geom_sum_mul ζ a
    linear_combination this
  rw [h1, norm_mul]
  have h2 : ‖∑ i ∈ Finset.range a, ζ ^ i‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_pow, norm_eq_one_of_pow_eq_one p hζ hN, one_pow]
  calc ‖∑ i ∈ Finset.range a, ζ ^ i‖ * ‖1 - ζ‖ ≤ 1 * ‖1 - ζ‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖1 - ζ‖ := one_mul _

lemma norm_one_sub_eq_of_isPrimitiveRoot {n : ℕ} {ζ μ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (hμ : IsPrimitiveRoot μ (p ^ n)) : ‖1 - μ‖ = ‖1 - ζ‖ := by
  have hne : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ n) := ⟨hne⟩
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
  obtain ⟨b, -, hb⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  apply le_antisymm (norm_one_sub_pow_le p hζ.pow_eq_one hne a)
  have := norm_one_sub_pow_le p hμ.pow_eq_one hne b
  rwa [hb] at this

theorem norm_sub_one_of_isPrimitiveRoot {n : ℕ} (hn : 0 < n) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) Ω, (1 - μ) := by
    have h1 := eval_one_cyclotomic_prime_pow (R := Ω) (p := p) k
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at h1
    rw [← h1]
    refine Finset.prod_congr rfl fun μ _ => ?_
    simp
  have hnorm : (p : ℝ)⁻¹ = ‖ζ - 1‖ ^ (p ^ (k + 1)).totient := by
    rw [← norm_natCast_p p, hprod, norm_prod, ← hζ.card_primitiveRoots, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun μ hμ => ?_
    rw [mem_primitiveRoots (pow_pos hp.pos _)] at hμ
    rw [norm_one_sub_eq_of_isPrimitiveRoot p hζ hμ, norm_sub_rev]
  have htot : (p ^ (k + 1)).totient ≠ 0 := (Nat.totient_pos.mpr (pow_pos hp.pos _)).ne'
  have h2 : ‖ζ - 1‖ = ((p : ℝ)⁻¹) ^ (((p ^ (k + 1)).totient : ℝ)⁻¹) := by
    rw [hnorm, Real.pow_rpow_inv_natCast (norm_nonneg _) htot]
  rw [h2, Real.inv_rpow (p_pos p).le, ← Real.rpow_neg (p_pos p).le]
  congr 1
  rw [neg_div, one_div]

def e (n : ℕ) : ℕ := (p ^ n).totient

lemma e_pos (n : ℕ) : 0 < e p n := Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos n)

def d (n : ℕ) : ℕ := if n = 0 then p - 1 else p

lemma d_pos (n : ℕ) : 0 < d p n := by
  unfold d; split_ifs
  · have := (Fact.out : p.Prime).one_lt; omega
  · exact (Fact.out : p.Prime).pos

lemma e_succ (n : ℕ) : e p (n + 1) = d p n * e p n := by
  have hp : p.Prime := Fact.out
  unfold e d
  split_ifs with h
  · subst h; simp [Nat.totient_prime hp]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
    ring

lemma cyclotomicTower_zero : L 0 = ⊥ := by
  apply le_antisymm _ bot_le
  unfold PadicAlgCl.cyclotomicTower
  rw [IntermediateField.adjoin_le_iff]
  intro x (hx : x ^ p ^ 0 = 1)
  rw [pow_zero, pow_one] at hx
  rw [hx]
  exact (⊥ : IntermediateField ℚ_[p] Ω).one_mem

lemma finrank_eq_e (n : ℕ) : Module.finrank ℚ_[p] (L n) = e p n := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [cyclotomicTower_zero, IntermediateField.finrank_bot]
    simp [e]
  · rw [(PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 n hn]
    unfold e
    rw [Nat.totient_prime_pow hp hn, mul_comm]

scoped instance finiteDimensional_L (n : ℕ) : FiniteDimensional ℚ_[p] (L n) :=
  Module.finite_of_finrank_pos (by rw [finrank_eq_e]; exact e_pos p n)

def VG (n : ℕ) : Prop :=
  ∀ c : Ω, c ∈ L n → c ≠ 0 → ∃ k : ℤ, ‖c‖ = (p : ℝ) ^ ((k : ℝ) / (e p n : ℝ))

lemma VG_zero : VG p 0 := by
  intro c hc hc0
  rw [cyclotomicTower_zero, IntermediateField.mem_bot] at hc
  obtain ⟨q, rfl⟩ := hc
  have hq : q ≠ 0 := by rintro rfl; exact hc0 (map_zero _)
  refine ⟨-q.valuation, ?_⟩
  rw [norm_algebraMap', Padic.norm_eq_zpow_neg_valuation hq]
  simp only [e, pow_zero, Nat.totient_one, Nat.cast_one, div_one]
  rw [← Real.rpow_intCast, Int.cast_neg]

lemma norm_term {n : ℕ} (hVG : VG p n) {π : Ω}
    (hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p (n + 1) : ℝ)))
    {c : Ω} (hc : c ∈ L n) (hc0 : c ≠ 0) (i : ℕ) :
    ∃ k : ℤ, ‖c * π ^ i‖ = (p : ℝ) ^ (((k * (d p n : ℤ) - (i : ℤ) : ℤ) : ℝ) / (e p (n + 1) : ℝ)) := by
  obtain ⟨k, hk⟩ := hVG c hc hc0
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow, hk, hπ, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le,
    ← Real.rpow_add (p_pos p)]
  congr 1
  have he : (e p (n + 1) : ℝ) = (d p n : ℝ) * (e p n : ℝ) := by exact_mod_cast e_succ p n
  have hen : (e p n : ℝ) ≠ 0 := by exact_mod_cast (e_pos p n).ne'
  have hd : (d p n : ℝ) ≠ 0 := by exact_mod_cast (d_pos p n).ne'
  rw [he]
  push_cast
  field_simp
  ring

lemma exponent_ne {n : ℕ} {i j : ℕ} (hi : i < d p n) (hj : j < d p n) (hij : i ≠ j) (k k' : ℤ) :
    (((k * (d p n : ℤ) - (i : ℤ) : ℤ) : ℝ) / (e p (n + 1) : ℝ)) ≠
      (((k' * (d p n : ℤ) - (j : ℤ) : ℤ) : ℝ) / (e p (n + 1) : ℝ)) := by
  intro h
  have hen : (e p (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (e_pos p (n + 1)).ne'
  rw [div_left_inj' hen] at h
  have h2 : (k * (d p n : ℤ) - (i : ℤ) : ℤ) = k' * (d p n : ℤ) - (j : ℤ) := by exact_mod_cast h
  have h3 : ((d p n : ℤ)) ∣ ((j : ℤ) - (i : ℤ)) := ⟨k' - k, by linarith⟩
  have h4 : ((j : ℤ) - (i : ℤ)) = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd h3
    rw [abs_lt]; constructor <;> omega
  exact hij (by omega)

lemma nnnorm_sum_eq_sup {n : ℕ} (hVG : VG p n) {π : Ω}
    (hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p (n + 1) : ℝ)))
    (c : ℕ → Ω) (hc : ∀ i < d p n, c i ∈ L n) :
    ‖∑ i ∈ Finset.range (d p n), c i * π ^ i‖₊ =
      (Finset.range (d p n)).sup fun i => ‖c i‖₊ * ‖π‖₊ ^ i := by
  classical
  set s := (Finset.range (d p n)).filter (fun i => c i ≠ 0) with hs
  have hsum : ∑ i ∈ Finset.range (d p n), c i * π ^ i = ∑ i ∈ s, c i * π ^ i := by
    rw [hs, Finset.sum_filter_of_ne]
    intro i _ hne hci
    exact hne (by rw [hci, zero_mul])
  have hpair : (s : Set ℕ).Pairwise fun i j => ‖c i * π ^ i‖₊ ≠ ‖c j * π ^ j‖₊ := by
    intro i hi j hj hij
    rw [Finset.mem_coe, hs, Finset.mem_filter, Finset.mem_range] at hi hj
    obtain ⟨k, hk⟩ := norm_term p hVG hπ (hc i hi.1) hi.2 i
    obtain ⟨k', hk'⟩ := norm_term p hVG hπ (hc j hj.1) hj.2 j
    intro heq
    have heq' : ‖c i * π ^ i‖ = ‖c j * π ^ j‖ := by
      have h := congrArg ((↑) : NNReal → ℝ) heq
      simpa only [coe_nnnorm] using h
    rw [hk, hk'] at heq'
    exact exponent_ne p hi.1 hj.1 hij k k' (rpow_p_injective p heq')
  rw [hsum, IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpair]
  simp only [nnnorm_mul, nnnorm_pow]
  apply le_antisymm
  · exact Finset.sup_mono (Finset.filter_subset _ _)
  · apply Finset.sup_le
    intro i hi
    by_cases hci : c i = 0
    · rw [hci, nnnorm_zero, zero_mul]; exact bot_le
    · exact Finset.le_sup (f := fun i => ‖c i‖₊ * ‖π‖₊ ^ i) (Finset.mem_filter.mpr ⟨hi, hci⟩)

def combo (n : ℕ) (π : Ω) : (Fin (d p n) → L n) →ₗ[ℚ_[p]] Ω where
  toFun v := ∑ i : Fin (d p n), ((v i : L n) : Ω) * π ^ (i : ℕ)
  map_add' v w := by
    simp only [Pi.add_apply, IntermediateField.coe_add, add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, IntermediateField.coe_smul, RingHom.id_apply, Finset.smul_sum,
      smul_mul_assoc]

lemma combo_apply (n : ℕ) (π : Ω) (v : Fin (d p n) → L n) :
    combo p n π v = ∑ i ∈ Finset.range (d p n),
      (fun i => if h : i < d p n then ((v ⟨i, h⟩ : L n) : Ω) else 0) i * π ^ i := by
  simp only [combo, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.2]

lemma exists_coeff {n n' : ℕ} (hn' : n' = n + 1) (hVG : VG p n) {π : Ω} (hπmem : π ∈ L n')
    (hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p n' : ℝ))) (y : Ω) (hy : y ∈ L n') :
    ∃ c : ℕ → Ω, (∀ i, c i ∈ L n) ∧ y = ∑ i ∈ Finset.range (d p n), c i * π ^ i := by
  classical
  subst hn'
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, norm_zero] at hπ
    exact (Real.rpow_pos_of_pos (p_pos p) _).ne hπ
  set Φ := combo p n π with hΦ

  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    set c : ℕ → Ω := fun i => if h : i < d p n then ((v ⟨i, h⟩ : L n) : Ω) else 0 with hcdef
    have hcmem : ∀ i < d p n, c i ∈ L n := by
      intro i hi; simp only [hcdef, dif_pos hi]; exact (v ⟨i, hi⟩).2
    have hsum : ∑ i ∈ Finset.range (d p n), c i * π ^ i = 0 := by
      rw [← hv, hΦ, combo_apply]
    have horth := nnnorm_sum_eq_sup p hVG hπ c hcmem
    rw [hsum, nnnorm_zero] at horth
    funext i
    have hle : ‖c i‖₊ * ‖π‖₊ ^ (i : ℕ) ≤ 0 := by
      rw [horth]
      exact Finset.le_sup (f := fun i => ‖c i‖₊ * ‖π‖₊ ^ i) (Finset.mem_range.mpr i.2)
    have hci : c i = 0 := by
      have h1 : ‖c i‖₊ * ‖π‖₊ ^ (i : ℕ) = 0 := le_antisymm hle bot_le
      rw [mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact nnnorm_eq_zero.mp h1
      · exact absurd (eq_zero_of_pow_eq_zero h1) (nnnorm_ne_zero_iff.mpr hπ0)
    simp only [hcdef, dif_pos i.2] at hci
    exact Subtype.ext hci

  set R₂ : Submodule ℚ_[p] Ω := LinearMap.range ((L (n + 1)).val.toLinearMap) with hR₂
  have hval_inj : Function.Injective ((L (n + 1)).val.toLinearMap) := fun a b h => Subtype.ext h
  have hle : LinearMap.range Φ ≤ R₂ := by
    rintro _ ⟨v, rfl⟩
    have hmem : Φ v ∈ L (n + 1) := by
      rw [hΦ]
      simp only [combo, LinearMap.coe_mk, AddHom.coe_mk]
      refine sum_mem fun i _ => mul_mem ?_ (pow_mem hπmem _)
      exact PadicAlgCl.cyclotomicTower_mono p (Nat.le_succ n) (v i).2
    exact ⟨⟨Φ v, hmem⟩, rfl⟩
  have hfin : Module.finrank ℚ_[p] (LinearMap.range Φ) = Module.finrank ℚ_[p] R₂ := by
    rw [LinearMap.finrank_range_of_inj hinj, hR₂, LinearMap.finrank_range_of_inj hval_inj,
      Module.finrank_pi_fintype, finrank_eq_e, finrank_eq_e, e_succ]
    simp
  have hEq : LinearMap.range Φ = R₂ := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hyR : y ∈ R₂ := ⟨⟨y, hy⟩, rfl⟩
  rw [← hEq] at hyR
  obtain ⟨v, hv⟩ := hyR
  refine ⟨fun i => if h : i < d p n then ((v ⟨i, h⟩ : L n) : Ω) else 0, fun i => ?_, ?_⟩
  · by_cases h : i < d p n
    · simp only [dif_pos h]; exact (v ⟨i, h⟩).2
    · simp only [dif_neg h]; exact zero_mem _
  · rw [← hv, hΦ, combo_apply]

lemma VG_succ {n n' : ℕ} (hn' : n' = n + 1) (hVG : VG p n) : VG p n' := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p n'
  have hn'pos : 0 < n' := by omega
  set π : Ω := ζ - 1 with hπdef
  have hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p n' : ℝ)) := norm_sub_one_of_isPrimitiveRoot p hn'pos hζ
  have hπmem : π ∈ L n' := sub_mem (mem_of_isPrimitiveRoot p n' hζ) (one_mem _)
  intro y hy hy0
  obtain ⟨c, hcmem, hyc⟩ := exists_coeff p hn' hVG hπmem hπ y hy
  subst hn'
  have horth := nnnorm_sum_eq_sup p hVG hπ c (fun i _ => hcmem i)
  rw [← hyc] at horth
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (d p n))
    (Finset.nonempty_range_iff.mpr (d_pos p n).ne') (fun i => ‖c i‖₊ * ‖π‖₊ ^ i)
  rw [hsup] at horth
  have hci₀ : c i₀ ≠ 0 := by
    intro h
    rw [h, nnnorm_zero, zero_mul, nnnorm_eq_zero] at horth
    exact hy0 horth
  obtain ⟨k, hk⟩ := norm_term p hVG hπ (hcmem i₀) hci₀ i₀
  refine ⟨k * (d p n : ℤ) - (i₀ : ℤ), ?_⟩
  rw [← hk, norm_mul, norm_pow]
  have h := congrArg ((↑) : NNReal → ℝ) horth
  simpa only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow] using h

theorem VG_all : ∀ n, VG p n := by
  intro n
  induction n with
  | zero => exact VG_zero p
  | succ n ih => exact VG_succ p rfl ih

def T (σ : Γ) (y : Ω) : Ω := ∑ j ∈ Finset.range p, (σ ^ j) y

lemma T_add (σ : Γ) (y y' : Ω) : T p σ (y + y') = T p σ y + T p σ y' := by
  simp only [T, map_add, Finset.sum_add_distrib]

lemma T_sum (σ : Γ) {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    T p σ (∑ i ∈ s, f i) = ∑ i ∈ s, T p σ (f i) := by
  simp only [T, map_sum]
  rw [Finset.sum_comm]

lemma pow_apply_of_apply_eq (σ : Γ) {a : Ω} (ha : σ a = a) (j : ℕ) : (σ ^ j) a = a := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]

lemma T_mul_of_fixed (σ : Γ) (a y : Ω) (ha : σ a = a) : T p σ (a * y) = a * T p σ y := by
  simp only [T, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_apply_of_apply_eq p σ ha j]

lemma T_mul_intCast (σ : Γ) (y : Ω) (z : ℤ) : T p σ (y * z) = T p σ y * z := by
  simp only [T, map_mul, map_intCast, Finset.sum_mul]

omit [Fact p.Prime] in

lemma pow_a_eq (k u a : ℕ) (ha : a = 1 + p ^ (k + 1) * u) (j : ℕ) :
    ∃ r : ℕ, a ^ j = 1 + p ^ (k + 1) * (j * u) + p ^ (k + 2) * r := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨p ^ k * j * u ^ 2 + r + p ^ (k + 1) * r * u, ?_⟩
      rw [pow_succ, hr, ha]
      ring

lemma T_zeta_pow {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hσ : σ ζ = ζ ^ a) (m : ℕ) :
    T p σ (ζ ^ m) = ζ ^ m * ∑ j ∈ Finset.range p, ((ζ ^ p ^ (k + 1)) ^ (m * u)) ^ j := by
  simp only [T, map_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_apply_eq_pow_pow p σ hσ j, ← pow_mul]
  obtain ⟨r, hr⟩ := pow_a_eq p k u a ha j
  rw [hr]
  have h1 : ζ ^ (p ^ (k + 2)) = 1 := hζ.pow_eq_one
  calc ζ ^ ((1 + p ^ (k + 1) * (j * u) + p ^ (k + 2) * r) * m)
      = ζ ^ m * (ζ ^ p ^ (k + 1)) ^ (m * u * j) * (ζ ^ p ^ (k + 2)) ^ (r * m) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ = ζ ^ m * ((ζ ^ p ^ (k + 1)) ^ (m * u)) ^ j := by
        rw [h1, one_pow, mul_one, ← pow_mul (ζ ^ p ^ (k + 1)) (m * u) j]

lemma T_zeta_pow_eq_zero {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hσ : σ ζ = ζ ^ a) {m : ℕ} (hm : ¬ p ∣ m * u) :
    T p σ (ζ ^ m) = 0 := by
  have hp : p.Prime := Fact.out
  rw [T_zeta_pow p hζ σ ha hσ m]
  have hξ : IsPrimitiveRoot (ζ ^ p ^ (k + 1)) p :=
    hζ.pow (pow_pos hp.pos _) (by rw [pow_succ])
  have hξ' : IsPrimitiveRoot ((ζ ^ p ^ (k + 1)) ^ (m * u)) p :=
    hξ.pow_of_coprime _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm |>.symm)
  rw [hξ'.geom_sum_eq_zero hp.one_lt, mul_zero]

lemma T_one (σ : Γ) : T p σ 1 = p := by
  simp [T]

theorem T_pi_pow {k : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (p ^ (k + 2))) (σ : Γ) {a u : ℕ}
    (ha : a = 1 + p ^ (k + 1) * u) (hu : ¬ p ∣ u) (hσ : σ ζ = ζ ^ a) {i : ℕ} (hi : i < p) :
    T p σ ((ζ - 1) ^ i) = (-1) ^ i * p := by
  have hp : p.Prime := Fact.out
  have hexp : (ζ - 1) ^ i = ∑ m ∈ Finset.range (i + 1), ζ ^ m * ((-1) ^ (i - m) * (i.choose m : ℤ) : ℤ) := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring
  rw [hexp, T_sum]
  rw [Finset.sum_range_succ']
  have hzero : ∀ m ∈ Finset.range i,
      T p σ (ζ ^ (m + 1) * ((-1) ^ (i - (m + 1)) * (i.choose (m + 1) : ℤ) : ℤ)) = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [T_mul_intCast, T_zeta_pow_eq_zero p hζ σ ha hσ, zero_mul]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact absurd (Nat.le_of_dvd (Nat.succ_pos m) h) (by omega)
    · exact hu h
  rw [Finset.sum_eq_zero hzero, zero_add, T_mul_intCast, pow_zero, T_one]
  push_cast
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  ring

theorem main (m : ℕ) (σ : Γ)
    (hσ : σ ∈ (L (m + 2)).fixingSubgroup) (hσ' : σ ∉ (L (m + 3)).fixingSubgroup)
    (y : Ω) (hy : y ∈ L (m + 3)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤
      ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p (m + 3)
  haveI : NeZero (p ^ (m + 3)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have ha' : σ ζ = ζ ^ a := ha.symm
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    rw [pow_zero] at ha'
    have h1 : ζ = 1 := by
      have := congrArg σ.symm ha'
      simpa using this
    have hone : (p ^ (m + 3) : ℕ) = 1 := by
      have := hζ.eq_orderOf
      rw [h1, orderOf_one] at this
      exact this
    have : 1 < p ^ (m + 3) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hdvd : p ^ (m + 2) ∣ a - 1 :=
    (mem_fixingSubgroup_iff_dvd p (by omega) hζ σ ha1 ha').mp hσ
  have hndvd : ¬ p ^ (m + 3) ∣ a - 1 := fun h =>
    hσ' ((mem_fixingSubgroup_iff_dvd p (le_refl _) hζ σ ha1 ha').mpr h)
  obtain ⟨u, hu⟩ := hdvd
  have hpu : ¬ p ∣ u := by
    rintro ⟨v, rfl⟩
    apply hndvd
    exact ⟨v, by rw [hu]; ring⟩
  have haeq : a = 1 + p ^ (m + 2) * u := by omega

  set π : Ω := ζ - 1 with hπdef
  have hπ : ‖π‖ = (p : ℝ) ^ (-(1 : ℝ) / (e p (m + 3) : ℝ)) :=
    norm_sub_one_of_isPrimitiveRoot p (by omega) hζ
  have hπmem : π ∈ L (m + 3) := sub_mem (mem_of_isPrimitiveRoot p (m + 3) hζ) (one_mem _)
  have hπpos : 0 < ‖π‖ := by rw [hπ]; exact Real.rpow_pos_of_pos (p_pos p) _
  have hπle : ‖π‖ ≤ 1 := by
    rw [hπ]
    apply Real.rpow_le_one_of_one_le_of_nonpos (one_lt_p p).le
    have : (0 : ℝ) < (e p (m + 3) : ℝ) := by exact_mod_cast e_pos p (m + 3)
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le

  have hVG := VG_all p (m + 2)
  obtain ⟨c, hcmem, hyc⟩ := exists_coeff p rfl hVG hπmem hπ y hy
  have hd : d p (m + 2) = p := by simp [d]
  rw [hd] at hyc
  have horth := nnnorm_sum_eq_sup p hVG hπ c (fun i _ => hcmem i)
  rw [hd, ← hyc] at horth

  have hci : ∀ i < p, ‖c i‖ * ‖π‖ ^ i ≤ ‖y‖ := by
    intro i hi
    have h1 : ‖c i‖₊ * ‖π‖₊ ^ i ≤ ‖y‖₊ := by
      rw [horth]
      exact Finset.le_sup (f := fun i => ‖c i‖₊ * ‖π‖₊ ^ i) (Finset.mem_range.mpr hi)
    exact_mod_cast h1

  have hT : ∑ i ∈ Finset.range p, (σ ^ i) y = (p : Ω) * ∑ i ∈ Finset.range p, (-1) ^ i * c i := by
    show T p σ y = _
    rw [hyc, T_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hfix : σ (c i) = c i :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (hcmem i)
    rw [T_mul_of_fixed p σ (c i) _ hfix, T_pi_pow p hζ σ haeq hpu ha' hi]
    ring
  rw [hT, norm_mul, norm_natCast_p, ← Padic.norm_p]

  have hB : ‖∑ i ∈ Finset.range p, (-1) ^ i * c i‖ ≤ ‖y‖ / ‖π‖ ^ (p - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [le_div_iff₀ (pow_pos hπpos _)]
    calc ‖c i‖ * ‖π‖ ^ (p - 1) ≤ ‖c i‖ * ‖π‖ ^ i :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hπpos.le hπle (by omega)) (norm_nonneg _)
      _ ≤ ‖y‖ := hci i hi

  have hpow : ‖y‖ / ‖π‖ ^ (p - 1) ≤ (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hπ, ← Real.rpow_natCast, ← Real.rpow_mul (p_pos p).le, ← Real.rpow_neg (p_pos p).le]
    apply Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le

    have he : (e p (m + 3) : ℝ) = ((p : ℝ) - 1) * (p : ℝ) ^ (m + 2) := by
      unfold e
      rw [Nat.totient_prime_pow_succ hp]
      have h1 : 1 ≤ p := hp.one_lt.le
      push_cast [Nat.cast_sub h1]
      ring
    rw [he]
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_p p; linarith
    have hpp : (0 : ℝ) < (p : ℝ) ^ (m + 1) := pow_pos (p_pos p) _
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le]; simp
    rw [hcast]
    have hsimp : -(-1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 2)) * ((p : ℝ) - 1)) = 1 / (p : ℝ) ^ (m + 2) := by
      field_simp
    rw [hsimp]
    apply one_div_le_one_div_of_le (by positivity)
    have : (p : ℝ) ^ (m + 2) = (p : ℝ) ^ (m + 1) * p := by ring
    rw [this]
    nlinarith [one_lt_p p]
  calc ‖(p : ℚ_[p])‖ * ‖∑ i ∈ Finset.range p, (-1) ^ i * c i‖
      ≤ ‖(p : ℚ_[p])‖ * (‖y‖ / ‖π‖ ^ (p - 1)) := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ ≤ ‖(p : ℚ_[p])‖ * ((p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ := by ring

end CTR
p2m_reactivate "P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower.CTR"

end
p2m_reactivate "P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower.CTR"

theorem solution (p : ℕ) [Fact p.Prime]
    (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p (m + 2)).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (m + 3)).fixingSubgroup)
    (y : PadicAlgCl p) (hy : y ∈ PadicAlgCl.cyclotomicTower p (m + 3)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤
      ‖(p : ℚ_[p])‖ * (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1))) * ‖y‖ :=
  CTR.main p m σ hσ hσ' y hy

end S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower
end P2MW
export P2MW.S_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower (solution)
