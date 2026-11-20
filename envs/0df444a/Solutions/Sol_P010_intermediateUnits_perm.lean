-- Prove2me | solution 1 for P010.intermediateUnits_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:52:21.210647+00:00
-- url     : https://prove2.me/submissions/97987bf3-94b4-4649-af00-3959ffc7b71e

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_intermediateEvenUnit_perm
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
theorem _root_.solution (n : ℕ) (pairs : List (ℕ × ℕ))
    (hn : 12 ≤ n)
    (hpairs : ∀ pair ∈ pairs,
      pair.1 ∈ intermediatePrimes n ∧
        pair.2 ∈ intermediatePrimes n) :
    (pairs.map (intermediateEvenUnit n)).flatten.Perm
      (classConcat n (pairs.flatMap (fun pq => [pq.1, pq.2]))) := by
  induction pairs with
  | nil => simp [classConcat]
  | cons pq rest ih =>
      have hpair := hpairs pq (by simp)
      have htail : ∀ pair ∈ rest,
          pair.1 ∈ intermediatePrimes n ∧
            pair.2 ∈ intermediatePrimes n := by
        intro pair hp
        exact hpairs pair (by simp [hp])
      have hunit := intermediateEvenUnit_perm n pq.1 pq.2
        hn hpair.1 hpair.2
      have hrest := ih htail
      simpa [classConcat, List.map_cons, List.flatten_cons,
        List.flatMap_cons] using hunit.append hrest
end P010
