-- Prove2me | solution 1 for P010.paired_leaf_with_core_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:41.005835+00:00
-- url     : https://prove2.me/submissions/963e0ee7-a8a3-4d94-8e34-f7150646335a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_join_prime_ended_paths
public import Theorems.Thm_P010_leaf_right_chain
public import Theorems.Thm_P010_unpaired_leaf_with_core_chain
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
theorem _root_.solution (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (core : List ℕ) (hc : NonCoprimeChain core)
    (he : EvenEnded core) :
    NonCoprimeChain ([p, 2 * p] ++ core ++ [2 * q, q]) := by
  obtain ⟨u, v, hu, hv, h2u, h2v⟩ := he
  have hleft : NonCoprimeChain ([p, 2 * p] ++ core) :=
    unpaired_leaf_with_core_chain p hp core hc ⟨u, v, hu, hv, h2u, h2v⟩
  apply join_prime_ended_paths 2 (by norm_num)
    ([p, 2 * p] ++ core) [2 * q, q] hleft (leaf_right_chain q hq)
  · intro x hx
    have heq : v = x := by
      have hlast : ([p, 2 * p] ++ core).getLast? = some v := by
        rw [List.getLast?_append_of_ne_nil]
        · exact hv
        · intro h
          simp [h] at hu
      have hx' : x ∈ (some v : Option ℕ) := by
        rw [← hlast]
        exact hx
      simpa using hx'
    simpa [← heq] using h2v
  · intro y hy
    have heq : 2 * q = y := by simpa using hy
    simpa [← heq] using (show 2 ∣ 2 * q from ⟨q, by omega⟩)
end P010
