-- Prove2me | solution 1 for P010.P010_universal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:51:13.692649+00:00
-- url     : https://prove2.me/submissions/88ea3033-782b-425c-9145-bd576c5c5ab8

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_middlePrimes_card
public import Theorems.Thm_P010_maximalNonCoprimeRuns_flatten
public import Theorems.Thm_P010_maximalNonCoprimeRuns_chains
public import Theorems.Thm_P010_maximalNonCoprimeRuns_length
public import Theorems.Thm_P010_isolatedVertices_card
public import Theorems.Thm_P010_permutation_mem_iff
public import Theorems.Thm_P010_noncoprime_cover_lower_counts
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
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n)
    (a : List ℕ) (ha : IsPermutation n a) :
    target n ≤ adjacentCount a := by
  cases a with
  | nil =>
      have hmem : 1 ∈ ([] : List ℕ) :=
        (permutation_mem_iff n [] ha 1).2 (by omega)
      simp at hmem
  | cons x xs =>
      let paths := maximalNonCoprimeRuns (x :: xs)
      have hcover : IsPermutation n paths.flatten := by
        simpa [paths, maximalNonCoprimeRuns_flatten] using ha
      have hchains : ∀ p ∈ paths, NonCoprimeChain p :=
        maximalNonCoprimeRuns_chains (x :: xs)
      obtain ⟨hdegree, hother⟩ :=
        noncoprime_cover_lower_counts n hn paths hcover hchains
      have hrun : paths.length = adjacentCount (x :: xs) + 1 :=
        maximalNonCoprimeRuns_length x xs
      have hi := isolatedVertices_card n
      have hm := middlePrimes_card n
      unfold target
      omega
end P010
