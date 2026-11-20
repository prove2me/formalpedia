-- Prove2me | solution 1 for P010.noncoprime_cover_lower_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:33.222173+00:00
-- url     : https://prove2.me/submissions/a44a8c74-34ad-4128-a0e3-7eaf9736d647

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_isolatedVertices_range
public import Theorems.Thm_P010_middlePrimes_range
public import Theorems.Thm_P010_permutation_mem_iff
public import Theorems.Thm_P010_permutation_nodup
public import Theorems.Thm_P010_permutation_filter_card
public import Theorems.Thm_P010_isolated_middle_path_weight
public import Theorems.Thm_P010_isolated_two_path_weight
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
private theorem weighted_capacity_flatten (ps : List (List ℕ))
    (f g : ℕ → Bool) (r s cap : ℕ)
    (h : ∀ p ∈ ps,
      r * (p.filter f).length + s * (p.filter g).length ≤ cap) :
    r * (ps.flatten.filter f).length +
        s * (ps.flatten.filter g).length ≤ cap * ps.length := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      have hp := h p (by simp)
      have ht : ∀ q ∈ rest,
          r * (q.filter f).length + s * (q.filter g).length ≤ cap := by
        intro q hq
        exact h q (by simp [hq])
      have hi := ih ht
      simp only [List.flatten_cons, List.filter_append,
        List.length_append, List.length_cons]
      nlinarith
end P010
end
end

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n)
    (paths : List (List ℕ))
    (hcover : IsPermutation n paths.flatten)
    (hchains : ∀ p ∈ paths, NonCoprimeChain p) :
    2 * (isolatedVertices n).card + (middlePrimes n).card ≤
        2 * paths.length ∧
      (isolatedVertices n).card + 1 ≤ paths.length := by
  have hnodup := permutation_nodup n paths.flatten hcover
  have hpath_nodup : ∀ p ∈ paths, p.Nodup :=
    (List.nodup_flatten.mp hnodup).1
  have hbound : ∀ p ∈ paths, ∀ t ∈ p, 0 < t ∧ t ≤ n := by
    intro p hp t ht
    have hmem := List.mem_flatten_of_mem hp ht
    have hr := (permutation_mem_iff n paths.flatten hcover t).1 hmem
    omega
  have hi : (paths.flatten.filter
      (fun t => decide (t ∈ isolatedVertices n))).length =
      (isolatedVertices n).card :=
    permutation_filter_card n paths.flatten hcover (isolatedVertices n)
      (fun x hx => isolatedVertices_range n x hx (by omega))
  have hm : (paths.flatten.filter
      (fun t => decide (t ∈ middlePrimes n))).length =
      (middlePrimes n).card :=
    permutation_filter_card n paths.flatten hcover (middlePrimes n)
      (fun x hx => middlePrimes_range n x hx)
  have htwo : (paths.flatten.filter
      (fun t => decide (t = 2))).length = 1 := by
    have hf := permutation_filter_card n paths.flatten hcover
        ({2} : Finset ℕ) (by
          intro x hx
          simp only [Finset.mem_singleton] at hx
          omega)
    simpa using hf
  have hw : 2 * (paths.flatten.filter
      (fun t => decide (t ∈ isolatedVertices n))).length +
      (paths.flatten.filter
      (fun t => decide (t ∈ middlePrimes n))).length ≤
      2 * paths.length := by
    have h := weighted_capacity_flatten paths
        (fun t => decide (t ∈ isolatedVertices n))
        (fun t => decide (t ∈ middlePrimes n)) 2 1 2 (by
          intro p hp
          simpa using isolated_middle_path_weight n p
            (hchains p hp) (hpath_nodup p hp) (hbound p hp))
    simpa using h
  have hw2 : (paths.flatten.filter
      (fun t => decide (t ∈ isolatedVertices n))).length +
      (paths.flatten.filter
      (fun t => decide (t = 2))).length ≤ paths.length := by
    have h := weighted_capacity_flatten paths
        (fun t => decide (t ∈ isolatedVertices n))
        (fun t => decide (t = 2)) 1 1 1 (by
          intro p hp
          simpa using isolated_two_path_weight n hn p
            (hchains p hp) (hpath_nodup p hp) (hbound p hp))
    simpa using h
  constructor <;> omega
end P010
