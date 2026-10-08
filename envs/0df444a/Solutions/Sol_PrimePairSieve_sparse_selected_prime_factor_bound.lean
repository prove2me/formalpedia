-- Prove2me | solution 1 for PrimePairSieve.sparse_selected_prime_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:33:13.220051+00:00
-- url     : https://prove2.me/submissions/b6b2edc6-c985-4a5e-93f4-3a9857115ed5

import Mathlib
import Definitions.Def_PrimePairSieve_ReciprocalLiteralWeight

open scoped BigOperators
set_option autoImplicit false

namespace PrimePairSieve
noncomputable section

def factor (p : ℕ) : ℝ := if p = 2 then 1 else 2 / ((p : ℝ) - 2)

lemma factor_eq (n : ℕ) (hsf : Squarefree n) :
    reciprocal_literal_weight n = ∏ p ∈ n.primeFactors, factor p := by
  simp [reciprocal_literal_weight, hsf, factor]

lemma factor_nonneg {p : ℕ} (hp : Nat.Prime p) : 0 ≤ factor p := by
  unfold factor
  split_ifs with h
  · norm_num
  · have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hr : (3 : ℝ) ≤ p := by exact_mod_cast h3
    apply div_nonneg (by norm_num)
    linarith

lemma factor_le_one {p : ℕ} (hp : Nat.Prime p) (hp3 : p ≠ 3) : factor p ≤ 1 := by
  unfold factor
  split_ifs with h
  · exact le_rfl
  · have h4 : 4 ≤ p := by have := hp.two_le; omega
    have hr : (4 : ℝ) ≤ p := by exact_mod_cast h4
    apply (div_le_one (by linarith)).mpr
    linarith

lemma product_le_two (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    (∏ p ∈ s, factor p) ≤ 2 := by
  classical
  by_cases h3 : 3 ∈ s
  · rw [← Finset.mul_prod_erase s factor h3]
    have hrest : (∏ p ∈ s.erase 3, factor p) ≤ 1 := by
      apply Finset.prod_le_one
      · intro p hp
        exact factor_nonneg (hs p (Finset.mem_of_mem_erase hp))
      · intro p hp
        exact factor_le_one (hs p (Finset.mem_of_mem_erase hp)) (Finset.mem_erase.mp hp).1
    rw [show factor 3 = 2 by norm_num [factor]]
    linarith
  · have hprod : (∏ p ∈ s, factor p) ≤ 1 := by
      apply Finset.prod_le_one
      · intro p hp
        exact factor_nonneg (hs p hp)
      · intro p hp
        exact factor_le_one (hs p hp) (by intro he; subst p; exact h3 hp)
    linarith

end
end PrimePairSieve

theorem solution (n p K : ℕ) (hK : 0 < K)
    (hselected : (1 : ℝ) / K ≤ PrimePairSieve.reciprocal_literal_weight n)
    (hp : p ∈ n.primeFactors) :
    p ≤ 4 * K + 2 := by
  classical
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hsf : Squarefree n := by
    by_contra h
    have hh : (0 : ℝ) < 1 / (K : ℝ) := by positivity
    simp [PrimePairSieve.reciprocal_literal_weight, h] at hselected
    linarith
  have hpr := Nat.prime_of_mem_primeFactors hp
  by_cases hp2 : p = 2
  · omega
  by_cases hp3 : p = 3
  · omega
  have h4 : 4 ≤ p := by have := hpr.two_le; omega
  have h2p : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
  have hppos : 0 < (p : ℝ) - 2 := by linarith
  have hrest := PrimePairSieve.product_le_two (n.primeFactors.erase p)
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
  have hweight : PrimePairSieve.reciprocal_literal_weight n ≤ 4 / ((p : ℝ) - 2) := by
    rw [PrimePairSieve.factor_eq n hsf, ← Finset.mul_prod_erase n.primeFactors PrimePairSieve.factor hp]
    calc
      _ ≤ PrimePairSieve.factor p * 2 :=
        mul_le_mul_of_nonneg_left hrest (PrimePairSieve.factor_nonneg hpr)
      _ = _ := by simp [PrimePairSieve.factor, hp2]; ring
  have hratio := hselected.trans hweight
  have hineq := (div_le_div_iff₀ hKR hppos).mp hratio
  have hbound : (p : ℝ) ≤ 4 * (K : ℝ) + 2 := by nlinarith
  exact_mod_cast hbound

#print axioms solution
