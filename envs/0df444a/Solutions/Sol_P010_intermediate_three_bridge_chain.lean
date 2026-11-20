-- Prove2me | solution 1 for P010.intermediate_three_bridge_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:33.645336+00:00
-- url     : https://prove2.me/submissions/69d47e2e-1b92-4e56-94ae-0c5f5e27473c

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_join_three_ended_paths
public import Theorems.Thm_P010_intermediate_prime_endpoints
public import Theorems.Thm_P010_three_class_bridge_vertices
public import Theorems.Thm_P010_orderedPrimeClass_chain
public import Theorems.Thm_P010_orderedPrimeClass_head
public import Theorems.Thm_P010_orderedPrimeClass_last
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
    NonCoprimeChain
      (orderedPrimeClass n 3 6 9 ++
       orderedPrimeClass n p (3 * p) (2 * p)) := by
  obtain ⟨h6, h9, _⟩ := three_class_bridge_vertices n hn
  obtain ⟨h2, h3, _⟩ :=
    intermediate_prime_endpoints n p hn hp hquarter hthird
  apply join_three_ended_paths
  · exact orderedPrimeClass_chain n 3 6 9 (by norm_num) h6 h9
  · exact orderedPrimeClass_chain n p (3 * p) (2 * p) hp h3 h2
  · intro x hx
    have heq : 9 = x := by
      simpa [orderedPrimeClass_last] using hx
    subst x
    exact ⟨3, rfl⟩
  · intro y hy
    have heq : 3 * p = y := by
      simpa [orderedPrimeClass_head] using hy
    subst y
    exact ⟨p, rfl⟩
end P010
