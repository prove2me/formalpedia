-- Prove2me | solution 1 for OpenMath.WOWII96.indepNum_le_one_of_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:43.614907+00:00
-- url     : https://prove2.me/submissions/d4c85452-95b7-4b98-b209-54717fb1f0ce

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_OpenMath_WOWII96
public import Theorems.Thm_OpenMath_card_le_indepNeighborsCard


set_option autoImplicit true
@[expose] public section
public section
open OpenMath OpenMath.WOWII96
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath.WOWII96
theorem _root_.solution {G : SimpleGraph α} (h : G.Connected)
    (hL : ∀ u, indepNeighborsCard G u ≤ 1) : G.indepNum ≤ 1 := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hlt
  have hnadj : ¬ G.Adj a b := hs.isIndepSet ha hb hab
  have hd : 1 < G.dist a b := h.one_lt_dist_of_ne_of_not_adj hab hnadj
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist a b
  obtain ⟨x, y, z, hxy, hyz, hxz, hne⟩ := q.exists_adj_adj_not_adj_ne hq hd
  have h2 : ({x, z} : Finset α).card ≤ indepNeighborsCard G y := by
    apply card_le_indepNeighborsCard
    · intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hxy.symm
      · exact hyz
    · intro p hp r hr hpr
      simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hr
      rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
      · exact absurd rfl hpr
      · exact hxz
      · exact fun h' => hxz h'.symm
      · exact absurd rfl hpr
  rw [card_pair hne] at h2
  have := hL y
  omega
end OpenMath.WOWII96
