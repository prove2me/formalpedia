-- Prove2me | solution 1 for P010.paired_intermediate_classes_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:06.935318+00:00
-- url     : https://prove2.me/submissions/5abe4436-23df-46ff-ae8e-d2a638701445

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_join_three_ended_paths
public import Theorems.Thm_P010_intermediate_prime_endpoints
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
theorem _root_.solution (n p q : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpquarter : n / 4 < p) (hpthird : p ≤ n / 3)
    (hqquarter : n / 4 < q) (hqthird : q ≤ n / 3) :
    NonCoprimeChain
      (orderedPrimeClass n p (2 * p) (3 * p) ++
       orderedPrimeClass n q (3 * q) (2 * q)) := by
  obtain ⟨hp2, hp3, _⟩ :=
    intermediate_prime_endpoints n p hn hp hpquarter hpthird
  obtain ⟨hq2, hq3, _⟩ :=
    intermediate_prime_endpoints n q hn hq hqquarter hqthird
  apply join_three_ended_paths
  · exact orderedPrimeClass_chain n p (2 * p) (3 * p) hp hp2 hp3
  · exact orderedPrimeClass_chain n q (3 * q) (2 * q) hq hq3 hq2
  · intro x hx
    have heq : 3 * p = x := by
      simpa [orderedPrimeClass_last] using hx
    subst x
    exact ⟨p, rfl⟩
  · intro y hy
    have heq : 3 * q = y := by
      simpa [orderedPrimeClass_head] using hy
    subst y
    exact ⟨q, rfl⟩
end P010
