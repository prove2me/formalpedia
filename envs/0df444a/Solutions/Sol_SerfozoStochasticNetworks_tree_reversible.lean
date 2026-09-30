-- Prove2me | solution 1 for SerfozoStochasticNetworks.tree_reversible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:23:18.802988+00:00
-- url     : https://prove2.me/submissions/a34bb3fe-04a5-49a9-aa10-4a1565324891

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

open Finset

/-- Kolmogorov's cut argument for a tree: the edge `{x, y}` is a bridge, so summing the balance
equations over the component `S` of `x` after deleting that edge leaves only the flows across
the edge. -/
theorem tr_main {E : Type*} [Fintype E] (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q)
    (hinv : IsInvariant q π) (htree : (commGraph q).IsTree) :
    DetailedBalance q π := by
  classical
  have hz : ∀ x y, q x y = 0 → q y x = 0 := by
    intro x y hxy
    rcases (hq y x).lt_or_eq with h | h
    · exact absurd ((htw y x).mp h) (by rw [hxy]; exact lt_irrefl 0)
    · exact h.symm
  have hadjiff : ∀ a b, (commGraph q).Adj a b ↔ a ≠ b ∧ (q a b ≠ 0 ∨ q b a ≠ 0) :=
    fun a b => SimpleGraph.fromRel_adj _ a b
  intro x y
  by_cases hxy0 : q x y = 0
  · rw [hxy0, hz x y hxy0, mul_zero, mul_zero]
  by_cases hxyeq : x = y
  · subst hxyeq; rfl
  have hadj : (commGraph q).Adj x y := (hadjiff x y).mpr ⟨hxyeq, Or.inl hxy0⟩
  have hbridge : (commGraph q).IsBridge s(x, y) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp htree.isAcyclic hadj
  rw [SimpleGraph.isBridge_iff] at hbridge
  let G' := (commGraph q).deleteEdges {s(x, y)}
  let S : Finset E := univ.filter (fun z => G'.Reachable x z)
  have hxS : x ∈ S := mem_filter.mpr ⟨mem_univ _, SimpleGraph.Reachable.refl x⟩
  have hyS : y ∉ S := fun h => hbridge (mem_filter.mp h).2
  -- the only rate across the cut is `q x y`
  have hcross : ∀ z ∈ S, ∀ w ∉ S, ¬ (z = x ∧ w = y) → q z w = 0 := by
    intro z hzS w hwS hne
    by_contra hzw
    have hzw' : z ≠ w := by rintro rfl; exact hwS hzS
    have hadj' : (commGraph q).Adj z w := (hadjiff z w).mpr ⟨hzw', Or.inl hzw⟩
    by_cases he : s(z, w) = s(x, y)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne ⟨rfl, rfl⟩
      · exact hyS hzS
    · have hadj'' : G'.Adj z w := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hadj', fun h => he (Set.mem_singleton_iff.mp h)⟩
      exact hwS (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hzS).2.trans hadj''.reachable⟩)
  have hbal : ∑ z ∈ S, π z * ∑ w, q z w = ∑ z ∈ S, ∑ w, π w * q w z := by
    refine sum_congr rfl fun z _ => ?_
    have := hinv z
    rwa [tsum_fintype, tsum_fintype] at this
  have hsplit1 : ∑ z ∈ S, π z * ∑ w, q z w =
      ∑ z ∈ S, ∑ w ∈ S, π z * q z w + ∑ z ∈ S, ∑ w ∈ Sᶜ, π z * q z w := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    rw [mul_sum, sum_add_sum_compl]
  have hsplit2 : ∑ z ∈ S, ∑ w, π w * q w z =
      ∑ z ∈ S, ∑ w ∈ S, π w * q w z + ∑ z ∈ S, ∑ w ∈ Sᶜ, π w * q w z := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_add_sum_compl]
  have hinner : ∑ z ∈ S, ∑ w ∈ S, π z * q z w = ∑ z ∈ S, ∑ w ∈ S, π w * q w z := sum_comm
  have hcut : ∑ z ∈ S, ∑ w ∈ Sᶜ, π z * q z w = ∑ z ∈ S, ∑ w ∈ Sᶜ, π w * q w z := by
    linarith
  have hyS' : y ∈ Sᶜ := mem_compl.mpr hyS
  have hL : ∑ z ∈ S, ∑ w ∈ Sᶜ, π z * q z w = π x * q x y := by
    rw [sum_eq_single_of_mem x hxS, sum_eq_single_of_mem y hyS']
    · intro w hw hwy
      rw [hcross x hxS w (mem_compl.mp hw) (fun h => hwy h.2), mul_zero]
    · intro z hz' hzx
      refine sum_eq_zero fun w hw => ?_
      rw [hcross z hz' w (mem_compl.mp hw) (fun h => hzx h.1), mul_zero]
  have hR : ∑ z ∈ S, ∑ w ∈ Sᶜ, π w * q w z = π y * q y x := by
    rw [sum_eq_single_of_mem x hxS, sum_eq_single_of_mem y hyS']
    · intro w hw hwy
      rw [hz x w (hcross x hxS w (mem_compl.mp hw) (fun h => hwy h.2)), mul_zero]
    · intro z hz' hzx
      refine sum_eq_zero fun w hw => ?_
      rw [hz z w (hcross z hz' w (mem_compl.mp hw) (fun h => hzx h.1)), mul_zero]
  rw [← hL, ← hR, hcut]

end SerfozoStochasticNetworks

open SerfozoStochasticNetworks

theorem solution {E : Type*} [Fintype E] (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hdiag : ∀ x, q x x = 0)
    (hπ : ∀ x, 0 < π x) (hinv : IsInvariant q π) (htree : (commGraph q).IsTree) :
    DetailedBalance q π :=
  tr_main q π hq htw hinv htree
