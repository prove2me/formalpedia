-- Prove2me | solution 1 for P010.small_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:45:59.706081+00:00
-- url     : https://prove2.me/submissions/0d0a0d3d-e7ab-4884-b5e9-7f040da8ecd6

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_smallWitness_certified
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
theorem _root_.solution (n : ℕ) (hn4 : 4 ≤ n) (hn11 : n ≤ 11) :
    ∃ a : List ℕ, IsPermutation n a ∧ adjacentCount a = target n := by
  obtain ⟨hperm, hcount⟩ := smallWitness_certified n (by omega) hn11
  refine ⟨smallWitness n, hperm, ?_⟩
  simpa [show ¬n ≤ 3 by omega] using hcount
end P010
