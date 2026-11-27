-- Prove2me | solution 1 for SizeRamsey.Plan.equality_max_degree_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:50.681807+00:00
-- url     : https://prove2.me/submissions/719b0158-ed3f-462b-9caa-b32f84387c04

module
public import Definitions.Def_SizeRamsey_Universal
public import Definitions.Def_SizeRamsey_Tightness
public import Theorems.Thm_SizeRamsey_Plan_erase_singleton_counts
public import Theorems.Thm_SizeRamsey_Plan_tau4_delete_vertices_le
public import Theorems.Thm_SizeRamsey_Plan_universal


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
    (ht : 4 * tau4 G = edgeCount G) :
    ∀ v, G.degree v ≤ 4 := by
  intro v
  have hdel : tau4 G ≤ tau4 (erase G {v}) + 1 := by
    have h := tau4_delete_vertices_le G {v} {v} subset_rfl (fun _ _ h => h)
    simpa using h
  have hcount := (erase_singleton_counts G v).1
  have hbound := universal (erase G {v})
  omega
end SizeRamsey.Plan
