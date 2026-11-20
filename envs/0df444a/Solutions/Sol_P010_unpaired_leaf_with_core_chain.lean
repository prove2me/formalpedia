-- Prove2me | solution 1 for P010.unpaired_leaf_with_core_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:11.542009+00:00
-- url     : https://prove2.me/submissions/e6d3ea1e-a25d-4fac-9d8d-0a8ffdb80fca

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_join_prime_ended_paths
public import Theorems.Thm_P010_leaf_left_chain
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
theorem _root_.solution (p : ℕ) (hp : Nat.Prime p)
    (core : List ℕ) (hc : NonCoprimeChain core)
    (he : EvenEnded core) :
    NonCoprimeChain ([p, 2 * p] ++ core) := by
  obtain ⟨u, v, hu, hv, h2u, h2v⟩ := he
  apply join_prime_ended_paths 2 (by norm_num)
    [p, 2 * p] core (leaf_left_chain p hp) hc
  · intro x hx
    have hxx : 2 * p = x := by simpa using hx
    subst x
    exact ⟨p, by omega⟩
  · intro y hy
    have hyy : u = y := by simpa [hu] using hy
    simpa [← hyy] using h2u
end P010
