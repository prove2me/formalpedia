-- Prove2me | solution 1 for P010.large_prime_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:46:24.250504+00:00
-- url     : https://prove2.me/submissions/e9ee04fc-525b-4124-8e98-88138a18a926

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_prime_mem_primeClass
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
    (hbig : n / 2 < p) (hle : p ≤ n) :
    primeClass n p = {p} := by
  ext m
  constructor
  · intro hm
    obtain ⟨t, htpos, htlt, hmt⟩ :=
      primeClass_multiple_below n p m 2 hm (by omega)
    have ht : t = 1 := by omega
    simp only [Finset.mem_singleton]
    simpa [ht] using hmt
  · intro hm
    have heq : m = p := Finset.mem_singleton.mp hm
    subst m
    exact prime_mem_primeClass n p hp hle
end P010
