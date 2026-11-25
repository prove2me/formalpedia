-- Prove2me | solution 1 for OpenMath.WOWII19.card_le_b_of_layered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:33.254978+00:00
-- url     : https://prove2.me/submissions/0f76f837-940e-4183-8089-58002c959ac1

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_induce_isBipartite_iff_exists_coloring


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath.WOWII19
theorem _root_.solution {G : SimpleGraph α} (v : α) (H : Finset α)
    (hH : ∀ x ∈ H, ∀ y ∈ H, G.Adj x y → G.dist v x ≠ G.dist v y) :
    H.card ≤ largestInducedBipartiteSubgraphSize G := by
  have hbip : (G.induce (H : Set α)).IsBipartite := by
    rw [induce_isBipartite_iff_exists_coloring]
    refine ⟨fun x => if Even (G.dist v x) then 0 else 1, ?_⟩
    intro x hx y hy hxy
    have hne := hH x hx y hy hxy
    dsimp only
    rcases hxy.diff_dist_adj (u := v) with h' | h' | h'
    · exact absurd h'.symm hne
    · rw [h']
      by_cases he : Even (G.dist v x)
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one]
    · have hx0 : G.dist v x ≠ 0 := by
        intro h0
        rw [h0] at h'
        exact hne (by omega)
      obtain ⟨k, hk⟩ : ∃ k, G.dist v x = k + 1 := ⟨G.dist v x - 1, by omega⟩
      rw [h', hk, Nat.add_sub_cancel]
      by_cases he : Even k
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one]
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨H, hbip, rfl⟩
end OpenMath.WOWII19
