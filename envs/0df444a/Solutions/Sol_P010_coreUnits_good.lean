-- Prove2me | solution 1 for P010.coreUnits_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:28.650363+00:00
-- url     : https://prove2.me/submissions/474d1ace-4fee-4abd-a666-4ba857494a01

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_smallEvenUnit_good
public import Theorems.Thm_P010_intermediateEvenUnit_good
public import Theorems.Thm_P010_threeEvenUnit_none_good
public import Theorems.Thm_P010_threeEvenUnit_some_good
public import Theorems.Thm_P010_splitPrimePairs_pair_mem
public import Theorems.Thm_P010_splitPrimePairs_spare_mem
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
    ∀ unit ∈ coreUnits n, NonCoprimeChain unit ∧ EvenEnded unit := by
  classical
  intro unit hu
  simp only [coreUnits, List.mem_cons, List.mem_append,
    List.mem_map] at hu
  rcases hu with hfirst | hsmall | hpaired
  · subst unit
    cases hs : (splitPrimePairs (intermediatePrimes n).toList).2 with
    | none =>
        exact threeEvenUnit_none_good n hn
    | some p =>
        have hp : p ∈ intermediatePrimes n := by
          apply Finset.mem_toList.mp
          exact splitPrimePairs_spare_mem
            (intermediatePrimes n).toList p hs
        exact threeEvenUnit_some_good n p hn hp
  · obtain ⟨p, hp, hunit⟩ := hsmall
    subst unit
    have hmem : p ∈ (n / 4).primesLE :=
      (Finset.mem_erase.mp (Finset.mem_toList.mp hp)).2
    obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hmem
    exact smallEvenUnit_good n p hprime (by omega)
  · obtain ⟨pair, hpair, hunit⟩ := hpaired
    subst unit
    obtain ⟨hp, hq⟩ := splitPrimePairs_pair_mem
      (intermediatePrimes n).toList pair hpair
    exact intermediateEvenUnit_good n pair.1 pair.2 hn
      (Finset.mem_toList.mp hp) (Finset.mem_toList.mp hq)
end P010
