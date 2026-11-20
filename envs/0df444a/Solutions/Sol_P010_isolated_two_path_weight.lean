-- Prove2me | solution 1 for P010.isolated_two_path_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:51.300876+00:00
-- url     : https://prove2.me/submissions/eefe3f6f-dc39-43a4-9b21-ab102fc94714

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_two_not_isolated
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
private theorem filtered_two_le_one (a : List ℕ) (hd : a.Nodup) :
    (a.filter (fun x => decide (x = 2))).length ≤ 1 := by
  have hf : (a.filter (fun x => decide (x = 2))).Nodup := hd.filter _
  have hsub : (a.filter (fun x => decide (x = 2))) ⊆ [2] := by
    intro x hx
    simp only [List.mem_singleton]
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    aesop
  have hle := List.Nodup.length_le_of_subset hf hsub
  simpa using hle
end P010
end
end

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) (a : List ℕ)
    (hc : NonCoprimeChain a) (hd : a.Nodup)
    (hb : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    (a.filter (fun t => decide (t ∈ isolatedVertices n))).length +
        (a.filter (fun t => decide (t = 2))).length ≤ 1 := by
  by_cases hex : ∃ p, p ∈ a ∧ p ∈ isolatedVertices n
  · obtain ⟨p, hp, hi⟩ := hex
    have heq := isolated_path_singleton n p a hi hc hd hp hb
    have hne : p ≠ 2 := by
      intro heq2
      apply two_not_isolated n hn
      simpa [heq2] using hi
    rw [heq]
    simp [hi, hne]
  · have hno : ∀ p ∈ a, p ∉ isolatedVertices n := by
      intro p hp hi
      exact hex ⟨p, hp, hi⟩
    have hnil := filter_finset_nil (isolatedVertices n) a hno
    have hcap := filtered_two_le_one a hd
    rw [hnil]
    simpa using hcap
end P010
