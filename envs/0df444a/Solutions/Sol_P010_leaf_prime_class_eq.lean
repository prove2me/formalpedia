-- Prove2me | solution 1 for P010.leaf_prime_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:46:32.401174+00:00
-- url     : https://prove2.me/submissions/e415a586-0c6d-4d2f-b94c-d289eff53aa5

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_prime_mem_primeClass
public import Theorems.Thm_P010_two_mul_prime_mem_class
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
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hthird : n / 3 < p) (hhalf : p ≤ n / 2) :
    primeClass n p = {p, 2 * p} := by
  ext m
  constructor
  · intro hm
    obtain ⟨t, htpos, htlt, hmt⟩ :=
      primeClass_multiple_below n p m 3 hm (by omega)
    have hcases : t = 1 ∨ t = 2 := by omega
    rcases hcases with ht | ht
    · simp [ht, hmt]
    · simp [ht, hmt]
  · intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with heq | heq
    · subst m
      exact prime_mem_primeClass n p hp (by omega)
    · subst m
      exact two_mul_prime_mem_class n p hp (by omega)
end P010
