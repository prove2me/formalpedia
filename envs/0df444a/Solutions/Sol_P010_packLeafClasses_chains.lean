-- Prove2me | solution 1 for P010.packLeafClasses_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:52:30.386178+00:00
-- url     : https://prove2.me/submissions/066aa197-bb45-4c5f-a3b4-a1d70ce1bb74

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_paired_leaf_classes_chain
public import Theorems.Thm_P010_unpaired_leaf_with_core_chain
public import Theorems.Thm_P010_paired_leaf_with_core_chain
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
theorem _root_.solution (core : List ℕ)
    (hc : NonCoprimeChain core) (he : EvenEnded core) :
    ∀ (leafs : List ℕ),
      (∀ p ∈ leafs, Nat.Prime p) →
      ∀ path ∈ packLeafClasses core leafs, NonCoprimeChain path := by
  intro leafs
  induction leafs using List.twoStepInduction with
  | nil =>
      intro _ path hm
      have hpath : path = core := by simpa [packLeafClasses] using hm
      subst path
      exact hc
  | singleton p =>
      intro hprime path hm
      have hpath : path = [p, 2 * p] ++ core := by
        simpa [packLeafClasses] using hm
      subst path
      exact unpaired_leaf_with_core_chain p
        (hprime p (by simp)) core hc he
  | cons_cons p q rest ih =>
      intro hprime path hm
      have hp : Nat.Prime p := hprime p (by simp)
      have hq : Nat.Prime q := hprime q (by simp)
      cases rest with
      | nil =>
          have hpath : path = [p, 2 * p] ++ core ++ [2 * q, q] := by
            simpa [packLeafClasses] using hm
          subst path
          exact paired_leaf_with_core_chain p q hp hq core hc he
      | cons r rs =>
          have hrest : ∀ x ∈ r :: rs, Nat.Prime x := by
            intro x hx
            exact hprime x (by simp [hx])
          have hmem : path ∈
              [p, 2 * p, 2 * q, q] :: packLeafClasses core (r :: rs) := by
            simpa only [packLeafClasses] using hm
          rcases List.mem_cons.mp hmem with heq | ht
          · subst path
            exact paired_leaf_classes_chain p q hp hq
          · exact ih hrest path ht
end P010
