-- Prove2me | solution 1 for P010.intermediateEvenUnit_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:51.703335+00:00
-- url     : https://prove2.me/submissions/97b9990a-7222-48ce-bdeb-2fa9a0dd8425

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_intermediate_prime_endpoints
public import Theorems.Thm_P010_orderedPrimeClass_perm
public import Theorems.Thm_P010_mem_intermediatePrimes
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
theorem _root_.solution (n p q : ℕ) (hn : 12 ≤ n)
    (hp : p ∈ intermediatePrimes n)
    (hq : q ∈ intermediatePrimes n) :
    (intermediateEvenUnit n (p, q)).Perm (classConcat n [p, q]) := by
  obtain ⟨hpp, hpquarter, hpthird⟩ := mem_intermediatePrimes.mp hp
  obtain ⟨hqq, hqquarter, hqthird⟩ := mem_intermediatePrimes.mp hq
  obtain ⟨hp2, hp3, hpneq⟩ :=
    intermediate_prime_endpoints n p hn hpp hpquarter hpthird
  obtain ⟨hq2, hq3, hqneq⟩ :=
    intermediate_prime_endpoints n q hn hqq hqquarter hqthird
  have h1 := orderedPrimeClass_perm n p (2 * p) (3 * p)
    hp2 hp3 hpneq
  have h2 := orderedPrimeClass_perm n q (3 * q) (2 * q)
    hq3 hq2 hqneq.symm
  simpa [intermediateEvenUnit, classConcat] using h1.append h2
end P010
