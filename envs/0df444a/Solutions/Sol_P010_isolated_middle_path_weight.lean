-- Prove2me | solution 1 for P010.isolated_middle_path_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:43.482288+00:00
-- url     : https://prove2.me/submissions/49c544ea-690a-4a34-8e4d-47271498355e

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_middle_primes_path_capacity
public import Theorems.Thm_P010_isolated_not_middle
public import Theorems.Thm_P010_isolated_path_singleton
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


section
@[expose] public section
namespace P010
private theorem filter_finset_nil (s : Finset ℕ) (a : List ℕ)
    (h : ∀ x ∈ a, x ∉ s) :
    a.filter (fun x => decide (x ∈ s)) = [] := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ∉ s := h x (by simp)
      have ht : ∀ y ∈ xs, y ∉ s := by
        intro y hy
        exact h y (by simp [hy])
      simpa [hx] using ih ht
end P010
end
end

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (a : List ℕ)
    (hc : NonCoprimeChain a) (hd : a.Nodup)
    (hb : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    2 * (a.filter (fun t => decide (t ∈ isolatedVertices n))).length +
        (a.filter (fun t => decide (t ∈ middlePrimes n))).length ≤ 2 := by
  by_cases hex : ∃ p, p ∈ a ∧ p ∈ isolatedVertices n
  · obtain ⟨p, hp, hi⟩ := hex
    have heq := isolated_path_singleton n p a hi hc hd hp hb
    rw [heq]
    have hm := isolated_not_middle n p hi
    simp [hi, hm]
  · have hno : ∀ p ∈ a, p ∉ isolatedVertices n := by
      intro p hp hi
      exact hex ⟨p, hp, hi⟩
    have hnil := filter_finset_nil (isolatedVertices n) a hno
    have hcap := middle_primes_path_capacity n a hc hd hb
    rw [hnil]
    simp only [List.length_nil, mul_zero, zero_add]
    exact hcap
end P010
