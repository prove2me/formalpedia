-- Prove2me | solution 1 for P010.prime_class_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:42:41.989378+00:00
-- url     : https://prove2.me/submissions/bfc57fe3-3471-48f1-881a-aa23c006b05a

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
theorem _root_.solution (p : ℕ) (hp : Nat.Prime p)
    (a : List ℕ) (hdiv : ∀ x ∈ a, p ∣ x) :
    NonCoprimeChain a := by
  have hpair : List.Pairwise (fun x y : ℕ => ¬Nat.Coprime x y) a := by
    induction a with
    | nil => exact List.Pairwise.nil
    | cons x xs ih =>
      apply List.Pairwise.cons
      · intro y hy
        exact common_prime_divisor_noncoprime hp
          (hdiv x (by simp)) (hdiv y (by simp [hy]))
      · exact ih (fun y hy => hdiv y (by simp [hy]))
  exact hpair.isChain
end P010
