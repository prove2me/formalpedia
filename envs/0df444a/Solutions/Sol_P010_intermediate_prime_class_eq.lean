-- Prove2me | solution 1 for P010.intermediate_prime_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:21.344379+00:00
-- url     : https://prove2.me/submissions/30ded627-8645-44c6-b46f-72da0fbf51c3

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_prime_mem_primeClass
public import Theorems.Thm_P010_two_mul_prime_mem_class
public import Theorems.Thm_P010_three_mul_prime_mem_class
public import Theorems.Thm_P010_primeClass_multiple_below
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hquarter : n / 4 < p)
    (hthird : p ≤ n / 3) :
    primeClass n p = {p, 2 * p, 3 * p} := by
  have hp3 : 3 ≤ p := by omega
  ext m
  constructor
  · intro hm
    obtain ⟨t, htpos, htlt, hmt⟩ :=
      primeClass_multiple_below n p m 4 hm (by omega)
    have hcases : t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases hcases with ht | ht | ht
    · simp [ht, hmt]
    · simp [ht, hmt]
    · simp [ht, hmt]
  · intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq | heq
    · subst m
      exact prime_mem_primeClass n p hp (by omega)
    · subst m
      exact two_mul_prime_mem_class n p hp (by omega)
    · subst m
      exact three_mul_prime_mem_class n p hp hp3 (by omega)
end P010
