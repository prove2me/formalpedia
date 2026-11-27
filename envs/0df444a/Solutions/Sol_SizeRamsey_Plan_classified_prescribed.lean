-- Prove2me | solution 1 for SizeRamsey.Plan.classified_prescribed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:34.023804+00:00
-- url     : https://prove2.me/submissions/0d6bda73-cd0f-4227-b858-826497d97ca2

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_small_graph_data
public import Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_iso

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
    PrescribedOptimal G := by
  obtain ⟨d1, d2, d3, d4⟩ := small_graph_data
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h
  · exact prescribedOptimal_iso e d1.2.2
  · exact prescribedOptimal_iso e d2.2.2
  · exact prescribedOptimal_iso e d3.2.2
  · exact prescribedOptimal_iso e d4.2.2
end SizeRamsey.Plan
