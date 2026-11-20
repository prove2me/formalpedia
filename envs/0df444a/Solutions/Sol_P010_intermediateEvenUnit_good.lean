-- Prove2me | solution 1 for P010.intermediateEvenUnit_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:51:57.375857+00:00
-- url     : https://prove2.me/submissions/d9789727-88be-4f8a-b291-10ad5ec8aa0a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_orderedPrimeClass_head
public import Theorems.Thm_P010_orderedPrimeClass_last
public import Theorems.Thm_P010_paired_intermediate_classes_chain
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
    NonCoprimeChain (intermediateEvenUnit n (p, q)) ∧
      EvenEnded (intermediateEvenUnit n (p, q)) := by
  obtain ⟨hpp, hpquarter, hpthird⟩ := mem_intermediatePrimes.mp hp
  obtain ⟨hqq, hqquarter, hqthird⟩ := mem_intermediatePrimes.mp hq
  have hc := paired_intermediate_classes_chain n p q hn
    hpp hqq hpquarter hpthird hqquarter hqthird
  let a := orderedPrimeClass n p (2 * p) (3 * p)
  let b := orderedPrimeClass n q (3 * q) (2 * q)
  have ha : a.head? = some (2 * p) := orderedPrimeClass_head ..
  have hb : b.getLast? = some (2 * q) := orderedPrimeClass_last ..
  have hane : a ≠ [] := by intro h; simp [h] at ha
  have hbne : b ≠ [] := by intro h; simp [h] at hb
  refine ⟨hc, 2 * p, 2 * q, ?_, ?_, ?_, ?_⟩
  · change (a ++ b).head? = some (2 * p)
    rw [List.head?_append_of_ne_nil a hane]
    exact ha
  · change (a ++ b).getLast? = some (2 * q)
    rw [List.getLast?_append_of_ne_nil a hbne]
    exact hb
  · exact ⟨p, by omega⟩
  · exact ⟨q, by omega⟩
end P010
