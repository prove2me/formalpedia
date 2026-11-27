-- Prove2me | solution 1 for SizeRamsey.Plan.induce_finset_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:31.696365+00:00
-- url     : https://prove2.me/submissions/4130e6f4-770f-4e05-9b40-4cf7e1373677

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_induce_degree_eq

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (D : Finset V) (v : (D : Set V)) :
    (G.induce (D : Set V)).degree v = ((G.neighborFinset v.val).filter (· ∈ D)).card := by
  convert induce_degree_eq G (D : Set V) v using 2
  ext w; simp
end SizeRamsey.Plan
