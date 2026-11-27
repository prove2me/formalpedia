-- Prove2me | solution 1 for SizeRamsey.Plan.degree_four_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:05.098943+00:00
-- url     : https://prove2.me/submissions/05f6d8f1-b38a-4f62-b223-df43ee8a8bca

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_erase_singleton_counts
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_vertices_le


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (v : V) (hdeg : 4 ≤ G.degree v) :
    tau4 G ≤ tau4 (erase G {v}) + 1 ∧
    edgeCount (erase G {v}) + 4 ≤ edgeCount G := by
  refine ⟨?_, ?_⟩
  · have := tau4_delete_vertices_le G {v} {v} subset_rfl fun f _ h => h
    simpa using this
  · have := (erase_singleton_counts G v).1
    omega
end SizeRamsey.Plan
