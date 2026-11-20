-- Prove2me | solution 1 for P010.orderedPrimeClass_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:46:43.307765+00:00
-- url     : https://prove2.me/submissions/aa29ccb3-5d6b-433e-ad2e-c06576584c21

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_orderedPrimeClass_mem
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
theorem _root_.solution (n p u v : ℕ)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p) :
    (orderedPrimeClass n p u v).toFinset = primeClass n p := by
  classical
  ext m
  simp only [List.mem_toFinset]
  constructor
  · exact orderedPrimeClass_mem n p u v m hu hv
  · intro hm
    by_cases hmu : m = u
    · subst m
      simp [orderedPrimeClass]
    by_cases hmv : m = v
    · subst m
      simp [orderedPrimeClass]
    · simp [orderedPrimeClass, hm, hmu, hmv]
end P010
