-- Prove2me | solution 1 for SizeRamsey.Plan.prescribedOptimal_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:00.720445+00:00
-- url     : https://prove2.me/submissions/6dd5072f-785e-4f66-b457-d3df64ace0d6

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_c4Transversal_map_iso
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
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (h : PrescribedOptimal H) :
    PrescribedOptimal G := by
  intro v
  obtain ⟨T, hv, hT, hcard⟩ := h (e v)
  refine ⟨T.map e.symm.toEquiv.toEmbedding, Finset.mem_map.mpr ⟨e v, hv, by simp⟩,
    c4Transversal_map_iso e hT, ?_⟩
  rw [Finset.card_map, hcard, tau4_iso e]
end SizeRamsey.Plan
