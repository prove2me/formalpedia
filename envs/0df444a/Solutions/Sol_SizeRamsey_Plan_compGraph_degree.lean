-- Prove2me | solution 1 for SizeRamsey.Plan.compGraph_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:03.490088+00:00
-- url     : https://prove2.me/submissions/3e425822-f5b5-4f98-b862-db2b1e31d448

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components

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
    (C : G.ConnectedComponent) (v : C.supp) :
    (compGraph G C).degree v = G.degree v.val := by
  refine SimpleGraph.degree_induce_of_neighborSet_subset fun w hw => ?_
  exact (C.mem_supp_congr_adj hw).mp v.2
end SizeRamsey.Plan
