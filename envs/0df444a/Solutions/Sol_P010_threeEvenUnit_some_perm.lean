-- Prove2me | solution 1 for P010.threeEvenUnit_some_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:57.651914+00:00
-- url     : https://prove2.me/submissions/b82b380f-ea33-4600-ace6-c7ce4c6abd69

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_intermediate_prime_endpoints
public import Theorems.Thm_P010_three_class_bridge_vertices
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
theorem _root_.solution (n p : ℕ) (hn : 12 ≤ n)
    (hp : p ∈ intermediatePrimes n) :
    (threeEvenUnit n (some p)).Perm (classConcat n [3, p]) := by
  obtain ⟨hpp, hquarter, hthird⟩ := mem_intermediatePrimes.mp hp
  obtain ⟨h6, h9, hneq⟩ := three_class_bridge_vertices n hn
  obtain ⟨h2, h3, hneq2⟩ :=
    intermediate_prime_endpoints n p hn hpp hquarter hthird
  have h1 := orderedPrimeClass_perm n 3 6 9 h6 h9 hneq
  have h2 := orderedPrimeClass_perm n p (3 * p) (2 * p)
    h3 h2 hneq2.symm
  simpa [threeEvenUnit, classConcat] using h1.append h2
end P010
