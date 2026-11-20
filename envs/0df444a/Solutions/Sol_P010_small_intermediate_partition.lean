-- Prove2me | solution 1 for P010.small_intermediate_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:03.840924+00:00
-- url     : https://prove2.me/submissions/2e17eb7d-2144-48c3-9761-d232489dd5fe

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_intermediatePrimes
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
theorem _root_.solution (n : ℕ) :
    (n / 4).primesLE ∪ intermediatePrimes n =
      (n / 3).primesLE := by
  ext p
  simp only [Finset.mem_union, Nat.mem_primesLE, mem_intermediatePrimes]
  constructor
  · rintro (⟨hle, hp⟩ | ⟨hp, _, hle⟩)
    · exact ⟨by omega, hp⟩
    · exact ⟨hle, hp⟩
  · rintro ⟨hle, hp⟩
    by_cases hs : p ≤ n / 4
    · exact Or.inl ⟨hs, hp⟩
    · exact Or.inr ⟨hp, by omega, hle⟩
end P010
