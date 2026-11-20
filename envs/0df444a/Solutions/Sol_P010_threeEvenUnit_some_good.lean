-- Prove2me | solution 1 for P010.threeEvenUnit_some_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:52:24.187787+00:00
-- url     : https://prove2.me/submissions/beb35eab-5bea-4db1-9bef-77fb16742a10

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_orderedPrimeClass_head
public import Theorems.Thm_P010_orderedPrimeClass_last
public import Theorems.Thm_P010_intermediate_three_bridge_chain
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
    NonCoprimeChain (threeEvenUnit n (some p)) ∧
      EvenEnded (threeEvenUnit n (some p)) := by
  obtain ⟨hpp, hquarter, hthird⟩ := mem_intermediatePrimes.mp hp
  have hc := intermediate_three_bridge_chain n p hn hpp hquarter hthird
  let a := orderedPrimeClass n 3 6 9
  let b := orderedPrimeClass n p (3 * p) (2 * p)
  have ha : a.head? = some 6 := orderedPrimeClass_head ..
  have hb : b.getLast? = some (2 * p) := orderedPrimeClass_last ..
  have hane : a ≠ [] := by intro h; simp [h] at ha
  have hbne : b ≠ [] := by intro h; simp [h] at hb
  refine ⟨hc, 6, 2 * p, ?_, ?_, ?_, ?_⟩
  · change (a ++ b).head? = some 6
    rw [List.head?_append_of_ne_nil a hane]
    exact ha
  · change (a ++ b).getLast? = some (2 * p)
    rw [List.getLast?_append_of_ne_nil a hbne]
    exact hb
  · exact ⟨3, by norm_num⟩
  · exact ⟨p, by omega⟩
end P010
