-- Prove2me | solution 1 for Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/610591bf-b593-5224-a46d-664965990308

import Mathlib
import Theorems.Thm_Polynomial_valuation_root_dichotomy_of_kroneckerShape
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KroneckerCount

open Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem pow_injective_of_one_lt {a : Γ₀} (ha : 1 < a) {m n : ℕ} (h : a ^ m = a ^ n) : m = n := by
  rcases lt_trichotomy m n with hmn | rfl | hmn
  · exact absurd h (pow_lt_pow_right₀ ha hmn).ne
  · rfl
  · exact absurd h (pow_lt_pow_right₀ ha hmn).ne'

section Shape

variable {q : ℕ} (hq : 1 < q) (x₀ c : K) (H : K[X]) (hHdeg : H.natDegree ≤ q)
include hq hHdeg

theorem main_eq : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) : K[X]) = (X - C (x₀ ^ q)) * (X ^ q - C x₀) := by ring

theorem main_monic : ((X - C (x₀ ^ q)) * (X ^ q - C x₀) : K[X]).Monic :=
  (monic_X_sub_C _).mul (monic_X_pow_sub_C x₀ (by omega))

theorem main_natDegree : ((X - C (x₀ ^ q)) * (X ^ q - C x₀) : K[X]).natDegree = q + 1 := by
  rw [(monic_X_sub_C _).natDegree_mul (monic_X_pow_sub_C x₀ (by omega)), natDegree_X_sub_C,
    natDegree_X_pow_sub_C, add_comm]

theorem pert_degree_lt : (C c * H).degree < ((X - C (x₀ ^ q)) * (X ^ q - C x₀) : K[X]).degree := by
  rw [Polynomial.degree_eq_natDegree (main_monic hq x₀ H hHdeg).ne_zero, main_natDegree hq x₀ H hHdeg]
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  refine lt_of_le_of_lt (add_le_add degree_C_le degree_le_natDegree) ?_
  rw [zero_add]
  exact_mod_cast Nat.lt_succ_of_le hHdeg

theorem monic : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).Monic := by
  rw [main_eq hq x₀ H hHdeg]
  exact (main_monic hq x₀ H hHdeg).add_of_left (pert_degree_lt hq x₀ c H hHdeg)

theorem natDegree_eq : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).natDegree = q + 1 := by
  rw [main_eq hq x₀ H hHdeg, natDegree_add_eq_left_of_degree_lt (pert_degree_lt hq x₀ c H hHdeg),
    main_natDegree hq x₀ H hHdeg]

theorem eval_zero : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).eval 0 = x₀ ^ (q + 1) + c * H.coeff 0 := by
  have hq0 : q ≠ 0 := by omega
  simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow, zero_pow hq0, sub_zero,
    coeff_zero_eq_eval_zero]
  ring

end Shape

theorem prod_map_valuation_roots {p : K[X]} (hp : p.Monic) (hs : p.Splits) :
    (p.roots.map v).prod = v (p.eval 0) := by
  conv_rhs => rw [hs.eq_prod_roots_of_monic hp]
  rw [eval_multiset_prod, Multiset.map_map]
  rw [show (p.roots.map v).prod = (p.roots.map (v.toMonoidWithZeroHom ∘ fun a => -a)).prod by
    congr 1; refine Multiset.map_congr rfl fun a _ => ?_; simp]
  rw [← Multiset.map_map, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [eval_sub, eval_X, eval_C]

theorem roots_filter_eq_singleton
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (hsplit : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).Splits)
    (hdich : ∀ y, ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y →
      v y = v x₀ ^ q ∨ v y ^ q = v x₀) :
    ∃ y₀ : K, (((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).roots.filter
      fun y => v y = v x₀ ^ q) = {y₀} := by
  classical
  set Φ : K[X] := (C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H with hΦ
  set X₀ := v x₀ with hX₀
  have hq0 : 0 < q := by omega
  have hmon : Φ.Monic := monic hq x₀ c H hHdeg
  have hΦ0 : Φ ≠ 0 := hmon.ne_zero
  have hcard : Φ.roots.card = q + 1 := by
    rw [← hsplit.natDegree_eq_card_roots, natDegree_eq hq x₀ c H hHdeg]

  have hv0 : v (Φ.eval 0) = X₀ ^ (q + 1) := by
    rw [eval_zero hq x₀ c H hHdeg, Valuation.map_add_eq_of_lt_left, map_pow]
    rw [map_pow, map_mul]
    calc v c * v (H.coeff 0) ≤ 1 * X₀ ^ q := mul_le_mul' hc (hHb 0 hq0)
      _ < X₀ ^ (q + 1) := by rw [one_mul]; exact pow_lt_pow_right₀ hx (Nat.lt_succ_self q)
  have hprod : (Φ.roots.map v).prod = X₀ ^ (q + 1) := by
    rw [prod_map_valuation_roots v hmon hsplit, hv0]

  set big : K → Prop := fun y => v y = X₀ ^ q with hbig
  set B := Φ.roots.filter big with hB
  set S := Φ.roots.filter fun y => ¬ big y with hS
  have hBS : B + S = Φ.roots := Multiset.filter_add_not _ _
  have hcardBS : B.card + S.card = q + 1 := by rw [← Multiset.card_add, hBS, hcard]
  have hBval : ∀ y ∈ B, v y = X₀ ^ q := fun y hy => (Multiset.mem_filter.mp hy).2
  have hSval : ∀ y ∈ S, v y ^ q = X₀ := by
    intro y hy
    obtain ⟨hyr, hnb⟩ := Multiset.mem_filter.mp hy
    exact ((hdich y ((mem_roots hΦ0).mp hyr)).resolve_left hnb)
  have hBprod : (B.map v).prod = (X₀ ^ q) ^ B.card := by
    rw [Multiset.map_congr rfl hBval, Multiset.map_const', Multiset.prod_replicate]
  have hSprod : (S.map v).prod ^ q = X₀ ^ S.card := by
    rw [← Multiset.prod_map_pow, Multiset.map_congr rfl hSval, Multiset.map_const', Multiset.prod_replicate]
  have hkey : X₀ ^ (q * (q + 1)) = X₀ ^ (q * q * B.card + S.card) := by
    rw [pow_mul', ← hprod, ← hBS, Multiset.map_add, Multiset.prod_add, mul_pow, hBprod, hSprod,
      ← pow_mul, ← pow_mul, ← pow_add]
    congr 1; ring
  have hnat : q * (q + 1) = q * q * B.card + S.card := pow_injective_of_one_lt hx hkey
  have hm : B.card = 1 := by
    have hS' : S.card = q + 1 - B.card := by omega
    rw [hS'] at hnat
    have hle : B.card ≤ q + 1 := by omega
    rcases Nat.lt_or_ge B.card 1 with h0 | h1
    · have : B.card = 0 := by omega
      rw [this, Nat.mul_zero, Nat.zero_add, Nat.sub_zero] at hnat
      have : q * q = 1 := by nlinarith
      nlinarith
    · rcases h1.eq_or_lt with h1 | h2
      · exact h1.symm
      · have h3 : q * (q + 1) ≥ q * q * 2 := by
          calc q * (q + 1) = q * q * B.card + (q + 1 - B.card) := hnat
            _ ≥ q * q * B.card := Nat.le_add_right _ _
            _ ≥ q * q * 2 := Nat.mul_le_mul_left _ h2
        nlinarith
  obtain ⟨y₀, hy₀⟩ := Multiset.card_eq_one.mp hm
  exact ⟨y₀, hy₀⟩

end KroneckerCount

theorem solution
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : Polynomial K) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (hsplit : ((Polynomial.C (x₀ ^ q) - Polynomial.X) * (Polynomial.C x₀ - Polynomial.X ^ q)
      + Polynomial.C c * H).Splits) :
    ∃ y₀ : K, (((Polynomial.C (x₀ ^ q) - Polynomial.X) * (Polynomial.C x₀ - Polynomial.X ^ q)
        + Polynomial.C c * H).roots.filter fun y => v y = v x₀ ^ q) = {y₀} :=
  KroneckerCount.roots_filter_eq_singleton v hq x₀ c hx hc H hHdeg hHb hHq hsplit fun y hy =>
    (Polynomial.valuation_root_dichotomy_of_kroneckerShape v hq x₀ c hx hc H hHdeg hHb hHq y hy).imp
      And.left And.left

end S_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape
end P2MW
export P2MW.S_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape (solution)
