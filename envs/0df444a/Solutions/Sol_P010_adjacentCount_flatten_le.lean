-- Prove2me | solution 1 for P010.adjacentCount_flatten_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:39.252399+00:00
-- url     : https://prove2.me/submissions/8b13ad62-dbd7-4bdd-aa57-0ee0135fbd03

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_chain_adjacentCount_zero
public import Theorems.Thm_P010_adjacentCount_append_le
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
theorem _root_.solution (paths : List (List ℕ))
    (hpaths : ∀ p ∈ paths, NonCoprimeChain p) :
    adjacentCount paths.flatten ≤ paths.length - 1 := by
  induction paths with
  | nil => simp [adjacentCount]
  | cons a rest ih =>
    cases rest with
    | nil =>
      have ha : NonCoprimeChain a := hpaths a (by simp)
      simpa [List.flatten, chain_adjacentCount_zero a ha]
    | cons b bs =>
      have ha : NonCoprimeChain a := hpaths a (by simp)
      have ht : ∀ p ∈ b :: bs, NonCoprimeChain p := by
        intro p hp
        exact hpaths p (by simp [hp])
      have hi := ih ht
      have hjoin := adjacentCount_append_le a (List.flatten (b :: bs))
      have hzero := chain_adjacentCount_zero a ha
      simp only [List.flatten_cons, List.length_cons] at *
      omega
end P010
