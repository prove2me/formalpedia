-- Prove2me | solution 1 for P010.permutation_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:45:22.128351+00:00
-- url     : https://prove2.me/submissions/ab0fd2db-cca4-40ba-8387-e5fe8e1b21d0

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_permutation_mem_iff
public import Theorems.Thm_P010_permutation_nodup
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
theorem _root_.solution (n : ℕ) (a : List ℕ)
    (ha : IsPermutation n a) (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x ∧ x ≤ n) :
    (a.filter (fun x => decide (x ∈ s))).length = s.card := by
  classical
  have hd : (a.filter (fun x => decide (x ∈ s))).Nodup :=
    (permutation_nodup n a ha).filter _
  have hsets : (a.filter (fun x => decide (x ∈ s))).toFinset = s := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · intro hx
      aesop
    · intro hx
      have hmem : x ∈ a := (permutation_mem_iff n a ha x).2 (hs x hx)
      aesop
  calc
    (a.filter (fun x => decide (x ∈ s))).length =
        (a.filter (fun x => decide (x ∈ s))).toFinset.card :=
          (List.toFinset_card_of_nodup hd).symm
    _ = s.card := congrArg Finset.card hsets
end P010
