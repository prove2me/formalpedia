-- Prove2me | solution 1 for OpenMath.WOWII19.sum_indepIn_le_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:01.94688+00:00
-- url     : https://prove2.me/submissions/27b2b0a3-adb0-49fa-a360-9f20c25e5a45

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_WOWII19_exists_indepIn
public import Theorems.Thm_OpenMath_WOWII19_card_le_b_of_layered

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace OpenMath.WOWII19
theorem _root_.solution (G : SimpleGraph α) (v : α) (e : ℕ) :
    ∑ i ∈ range (e + 1), indepIn G (layer G v i) ≤ largestInducedBipartiteSubgraphSize G := by
  classical
  have hex := fun i => exists_indepIn G (layer G v i)
  choose s hsT hsind hscard using hex
  have hdisj : (↑(range (e + 1)) : Set ℕ).PairwiseDisjoint s := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    have h1 := hsT i hxi
    have h2 := hsT j hxj
    simp only [layer, mem_filter, mem_univ, true_and] at h1 h2
    exact hij (h1.symm.trans h2)
  have hcard : ((range (e + 1)).biUnion s).card = ∑ i ∈ range (e + 1), indepIn G (layer G v i) := by
    rw [card_biUnion hdisj]
    exact sum_congr rfl fun i _ => hscard i
  rw [← hcard]
  apply card_le_b_of_layered v
  intro x hx y hy hxy hdist
  obtain ⟨i, -, hxi⟩ := mem_biUnion.mp hx
  obtain ⟨j, -, hyj⟩ := mem_biUnion.mp hy
  have h1 := hsT i hxi
  have h2 := hsT j hyj
  simp only [layer, mem_filter, mem_univ, true_and] at h1 h2
  have hij : i = j := by rw [← h1, ← h2, hdist]
  subst hij
  exact hsind i hxi hyj hxy.ne hxy
end OpenMath.WOWII19
