-- Prove2me | solution 1 for P010.middle_primes_path_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:39.646977+00:00
-- url     : https://prove2.me/submissions/64eada46-450f-4728-938f-13465cccaaef

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_middle_primes_tail_at_most_one
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
theorem _root_.solution (n : ℕ) (a : List ℕ)
    (hchain : NonCoprimeChain a)
    (hnodup : a.Nodup)
    (hbound : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    (a.filter (fun t => decide (t ∈ middlePrimes n))).length ≤ 2 := by
  cases a with
  | nil =>
      simp
  | cons x xs =>
      cases xs with
      | nil =>
          by_cases hx : x ∈ middlePrimes n <;> simp [hx]
      | cons y ys =>
          have htail :=
            middle_primes_tail_at_most_one n x y ys hchain hnodup hbound
          by_cases hx : x ∈ middlePrimes n
          · simpa [hx] using Nat.succ_le_succ htail
          · have hsmall : ((y :: ys).filter
                (fun t => decide (t ∈ middlePrimes n))).length ≤ 2 :=
              htail.trans (by omega)
            simpa [hx] using hsmall
end P010
