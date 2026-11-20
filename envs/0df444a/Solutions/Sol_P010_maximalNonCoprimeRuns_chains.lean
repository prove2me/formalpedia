-- Prove2me | solution 1 for P010.maximalNonCoprimeRuns_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:36:08.326176+00:00
-- url     : https://prove2.me/submissions/ba40784a-f7b0-4524-9606-f2c19e01a324

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
theorem _root_.solution (a : List ℕ) :
    ∀ p ∈ maximalNonCoprimeRuns a, NonCoprimeChain p := by
  intro p hp
  have hc : List.IsChain
      (fun (x y : ℕ) => (decide (¬Nat.Coprime x y)) = true) p := by
    exact List.isChain_of_mem_splitBy (show
      p ∈ a.splitBy (fun x y => decide (¬Nat.Coprime x y)) from hp)
  simpa [NonCoprimeChain] using hc
end P010
