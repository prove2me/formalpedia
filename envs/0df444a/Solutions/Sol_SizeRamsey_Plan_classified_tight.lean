-- Prove2me | solution 1 for SizeRamsey.Plan.classified_tight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:37:32.12981+00:00
-- url     : https://prove2.me/submissions/18e9cac3-0916-4851-8977-96f9196b44d2

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_small_graph_data
public import Theorems.Thm_SizeRamsey_Plan_edgeCount_iso
public import Theorems.Thm_SizeRamsey_tau4_iso


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : Classified G) :
    Tight G := by
  obtain ⟨d1, d2, d3, d4⟩ := small_graph_data
  unfold Tight
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h <;> rw [tau4_iso e, edgeCount_iso e]
  · rw [d1.1, d1.2.1]
  · rw [d2.1, d2.2.1]
  · rw [d3.1, d3.2.1]
  · rw [d4.1, d4.2.1]
end SizeRamsey.Plan
