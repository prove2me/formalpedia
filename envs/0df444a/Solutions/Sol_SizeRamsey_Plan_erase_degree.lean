-- Prove2me | solution 1 for SizeRamsey.Plan.erase_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:10.963946+00:00
-- url     : https://prove2.me/submissions/6bd78483-a959-413a-874a-0cf3e9ec7ed8

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_erase_degree_eq

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
    (D : Finset V) (v : {x : V // x ∉ D}) :
    (erase G D).degree v +
      (G.neighborFinset v.val ∩ D).card = G.degree v.val := by
  rw [erase_degree_eq, ← Finset.filter_mem_eq_inter, ← G.card_neighborFinset_eq_degree, add_comm]
  exact Finset.card_filter_add_card_filter_not _
end SizeRamsey.Plan
