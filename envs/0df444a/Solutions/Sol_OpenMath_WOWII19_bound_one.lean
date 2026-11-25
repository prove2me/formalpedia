-- Prove2me | solution 1 for OpenMath.WOWII19.bound_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:43.046411+00:00
-- url     : https://prove2.me/submissions/38abde61-7a5a-4b6b-a460-18135e0270eb

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_WOWII19_sum_indepIn_le_b
public import Theorems.Thm_OpenMath_WOWII19_one_le_indepIn_layer
public import Theorems.Thm_OpenMath_WOWII19_indepNeighborsCard_le_indepIn_layer_one

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}
namespace OpenMath.WOWII19
theorem _root_.solution (h : G.Connected) (v : α) (he : 1 ≤ ecc G v) :
    indepNeighborsCard G v + ecc G v ≤ largestInducedBipartiteSubgraphSize G := by
  refine le_trans ?_ (sum_indepIn_le_b G v (ecc G v))
  obtain ⟨k, hk⟩ : ∃ k, ecc G v = k + 1 := ⟨ecc G v - 1, by omega⟩
  rw [hk, sum_range_succ', sum_range_succ']
  have h0 : 1 ≤ indepIn G (layer G v 0) := one_le_indepIn_layer h v (by omega)
  have h1 := indepNeighborsCard_le_indepIn_layer_one (G := G) v
  have hrest : ∑ i ∈ range k, 1 ≤ ∑ i ∈ range k, indepIn G (layer G v (i + 1 + 1)) :=
    sum_le_sum fun i hi => one_le_indepIn_layer h v (by simp at hi; omega)
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hrest
  simp only [zero_add] at h1 h0 ⊢
  omega
end OpenMath.WOWII19
