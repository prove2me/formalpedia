-- Prove2me | solution 1 for P010.packLeafClasses_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:48:01.339113+00:00
-- url     : https://prove2.me/submissions/1741a385-13cb-4e56-bdba-e3e82033ad6d

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
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
theorem _root_.solution (core : List ℕ) :
    ∀ leafs : List ℕ,
      (packLeafClasses core leafs).length =
        max 1 ((leafs.length + 1) / 2) := by
  intro leafs
  induction leafs using List.twoStepInduction with
  | nil =>
      norm_num [packLeafClasses]
  | singleton p =>
      norm_num [packLeafClasses]
  | cons_cons p q rest ih =>
      cases rest with
      | nil =>
          norm_num [packLeafClasses]
      | cons r rs =>
          have hi := ih
          simp only [packLeafClasses, List.length_cons] at hi ⊢
          omega
end P010
