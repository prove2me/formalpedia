-- Prove2me | solution 1 for P010.splitPrimePairs_recompose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:33:56.190186+00:00
-- url     : https://prove2.me/submissions/feddadbf-048c-482b-8d31-5035b8d1758f

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
theorem _root_.solution :
    ∀ ps : List ℕ,
      (splitPrimePairs ps).1.flatMap (fun pq => [pq.1, pq.2]) ++
        (splitPrimePairs ps).2.toList = ps := by
  intro ps
  induction ps using List.twoStepInduction with
  | nil => rfl
  | singleton p => rfl
  | cons_cons p q rest ih =>
      simp only [splitPrimePairs, List.flatMap_cons, List.append_assoc]
      simpa using congrArg (fun t => p :: q :: t) ih
end P010
