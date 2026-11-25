-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.card_multiLe_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:31.417833+00:00
-- url     : https://prove2.me/submissions/9c47aa73-c118-4b28-b0c1-e0cf70cb199a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_mem_multiLe_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
open Finset
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n j : ℕ) :
    (multiLe (n + 1) j).card = ∑ a ∈ range (j + 1), (multiLe n (j - a)).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij' (fun α _ => (⟨α 0, Fin.tail α⟩ : Σ _ : ℕ, Fin n → ℕ))
    (fun p _ => (Fin.cons p.1 p.2 : Fin (n + 1) → ℕ)) ?_ ?_ ?_ ?_
  · intro α hα
    simp only [mem_multiLe_iff, Fin.sum_univ_succ] at hα
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff, Fin.tail]
    exact ⟨by omega, by omega⟩
  · rintro ⟨a, β⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range, mem_multiLe_iff] at hp
    simp only [mem_multiLe_iff, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    omega
  · intro α _
    exact Fin.cons_self_tail α
  · rintro ⟨a, β⟩ _
    simp only [Fin.cons_zero, Fin.tail_cons]
end ReciprocityTheory.L2DbarEstimates.Y
