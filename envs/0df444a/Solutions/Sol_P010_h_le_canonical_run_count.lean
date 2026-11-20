-- Prove2me | solution 1 for P010.h_le_canonical_run_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:03.804702+00:00
-- url     : https://prove2.me/submissions/beac8a59-52ce-4b95-bab2-d64f21ca7826

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_h_le_of_noncoprime_cover
public import Theorems.Thm_P010_maximalNonCoprimeRuns_flatten
public import Theorems.Thm_P010_maximalNonCoprimeRuns_chains
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
    (ha : IsPermutation n a) :
    h n ≤ (maximalNonCoprimeRuns a).length - 1 := by
  apply h_le_of_noncoprime_cover n (maximalNonCoprimeRuns a)
  · simpa [maximalNonCoprimeRuns_flatten] using ha
  · exact maximalNonCoprimeRuns_chains a
end P010
