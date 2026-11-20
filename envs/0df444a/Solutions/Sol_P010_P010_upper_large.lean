-- Prove2me | solution 1 for P010.P010_upper_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:59:13.198459+00:00
-- url     : https://prove2.me/submissions/7913287b-0e32-4ca4-99b9-8bd8a2eb34eb

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_largePrimes_card
public import Theorems.Thm_P010_middlePrimes_card
public import Theorems.Thm_P010_adjacentCount_flatten_le
public import Theorems.Thm_P010_optimalCover_chains
public import Theorems.Thm_P010_optimalCover_length
public import Theorems.Thm_P010_optimalCover_isPermutation
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
theorem _root_.solution (n : ℕ) (hn : 12 ≤ n) :
    ∃ a : List ℕ, IsPermutation n a ∧
      adjacentCount a ≤ target n := by
  let paths := optimalCover n
  have hc : IsPermutation n paths.flatten :=
    optimalCover_isPermutation n hn
  have hg : ∀ p ∈ paths, NonCoprimeChain p :=
    optimalCover_chains n hn
  have hcount : adjacentCount paths.flatten ≤ paths.length - 1 :=
    adjacentCount_flatten_le paths hg
  have hlen : paths.length = target n + 1 := by
    dsimp [paths]
    rw [optimalCover_length, largePrimes_card, middlePrimes_card]
    unfold target
    omega
  refine ⟨paths.flatten, hc, ?_⟩
  have heq : paths.length - 1 = target n := by omega
  simpa only [heq] using hcount
end P010
