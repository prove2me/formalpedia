-- Prove2me | solution 1 for P010.optimalCover_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:57:58.656761+00:00
-- url     : https://prove2.me/submissions/d92cc377-100b-4d0c-bd4c-cd90bf20f272

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_middlePrimes
public import Theorems.Thm_P010_packLeafClasses_chains
public import Theorems.Thm_P010_corePath_chain_even
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
    ∀ path ∈ optimalCover n, NonCoprimeChain path := by
  classical
  obtain ⟨hcore, heven⟩ := corePath_chain_even n hn
  have hpack : ∀ path ∈
      packLeafClasses (corePath n) (middlePrimes n).toList,
      NonCoprimeChain path := by
    apply packLeafClasses_chains (corePath n) hcore heven
    intro p hp
    exact (mem_middlePrimes.mp (Finset.mem_toList.mp hp)).1
  intro path hp
  simp only [optimalCover, List.mem_append, List.mem_singleton,
    List.mem_map] at hp
  rcases hp with (h1 | ⟨p, _, hpath⟩) | hpackmem
  · subst path
    simp [NonCoprimeChain]
  · subst path
    simp [NonCoprimeChain]
  · exact hpack path hpackmem
end P010
