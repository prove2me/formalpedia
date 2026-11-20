-- Prove2me | solution 1 for P010.paired_leaf_classes_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:54.525635+00:00
-- url     : https://prove2.me/submissions/b7d52033-f402-4b3f-b9f2-9d7cc3b19454

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_common_prime_divisor_noncoprime
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
theorem _root_.solution (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    NonCoprimeChain [p, 2 * p, 2 * q, q] := by
  simp only [NonCoprimeChain, List.isChain_cons_cons,
    List.IsChain.singleton, and_true]
  refine ⟨?_, ?_, ?_⟩
  · exact common_prime_divisor_noncoprime hp (dvd_refl p)
      ⟨2, by omega⟩
  · exact common_prime_divisor_noncoprime
      (by norm_num : Nat.Prime 2)
      ⟨p, by omega⟩ ⟨q, by omega⟩
  · exact common_prime_divisor_noncoprime hq
      ⟨2, by omega⟩ (dvd_refl q)
end P010
