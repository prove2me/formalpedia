-- Prove2me | solution 1 for P010.three_class_bridge_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:38:17.007391+00:00
-- url     : https://prove2.me/submissions/932239bf-28f1-4581-a5dd-a41dea3b7f99

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_two_mul_prime_mem_class
public import Theorems.Thm_P010_three_mul_prime_mem_class
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
theorem _root_.solution (n : ℕ) (hn : 12 ≤ n) :
    6 ∈ primeClass n 3 ∧ 9 ∈ primeClass n 3 ∧ 6 ≠ 9 := by
  have hp : Nat.Prime 3 := by norm_num
  constructor
  · simpa using two_mul_prime_mem_class n 3 hp (by omega)
  constructor
  · simpa using three_mul_prime_mem_class n 3 hp (by omega) (by omega)
  · norm_num
end P010
