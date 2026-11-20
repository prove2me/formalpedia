-- Prove2me | solution 1 for P010.middle_primes_tail_at_most_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:43:21.171856+00:00
-- url     : https://prove2.me/submissions/ca6ee185-7132-4921-a3de-20b4a5a7ced8

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_middle_prime_unique_neighbor
public import Theorems.Thm_P010_mem_middlePrimes
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
theorem _root_.solution (n x y : ℕ) (xs : List ℕ)
    (hchain : NonCoprimeChain (x :: y :: xs))
    (hnodup : (x :: y :: xs).Nodup)
    (hbound : ∀ t ∈ x :: y :: xs, 0 < t ∧ t ≤ n) :
    ((y :: xs).filter (fun t => decide (t ∈ middlePrimes n))).length ≤ 1 := by
  induction xs generalizing x y with
  | nil =>
      by_cases hy : y ∈ middlePrimes n <;> simp [hy]
  | cons z zs ih =>
      have hy_not_middle : y ∉ middlePrimes n := by
        intro hy
        obtain ⟨hprime, hthird, _⟩ := mem_middlePrimes.mp hy
        have hxy : ¬Nat.Coprime x y :=
          (List.isChain_cons.mp hchain).1 y (by simp)
        have hyz : ¬Nat.Coprime y z :=
          (List.isChain_cons.mp (List.isChain_cons.mp hchain).2).1 z (by simp)
        have hyx : ¬Nat.Coprime y x := by
          intro hc
          exact hxy hc.symm
        have hx_ne_y : x ≠ y := by
          intro heq
          exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
        have hx_ne_z : x ≠ z := by
          intro heq
          exact (List.nodup_cons.mp hnodup).1 (by simp [heq])
        have hz_ne_y : z ≠ y := by
          intro heq
          exact (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
            (by simp [heq])
        obtain ⟨hxpos, hxle⟩ := hbound x (by simp)
        obtain ⟨hzpos, hzle⟩ := hbound z (by simp)
        have hx : x = 2 * y :=
          middle_prime_unique_neighbor hprime hthird hxpos hxle hx_ne_y hyx
        have hz : z = 2 * y :=
          middle_prime_unique_neighbor hprime hthird hzpos hzle hz_ne_y hyz
        exact hx_ne_z (hx.trans hz.symm)
      have hchain' : NonCoprimeChain (y :: z :: zs) :=
        (List.isChain_cons.mp hchain).2
      have hnodup' : (y :: z :: zs).Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hbound' : ∀ t ∈ y :: z :: zs, 0 < t ∧ t ≤ n := by
        intro t ht
        exact hbound t (by simp [ht])
      have htail := ih y z hchain' hnodup' hbound'
      simpa [hy_not_middle] using htail
end P010
