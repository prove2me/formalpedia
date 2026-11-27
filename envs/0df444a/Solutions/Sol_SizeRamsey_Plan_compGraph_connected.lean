-- Prove2me | solution 1 for SizeRamsey.Plan.compGraph_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:22:18.495055+00:00
-- url     : https://prove2.me/submissions/6b35d116-8c84-4ac9-9903-b6cac704fe53

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
omit [Fintype V]
namespace SizeRamsey.Plan
theorem _root_.solution (C : G.ConnectedComponent) :
    (compGraph G C).Connected := by
  exact C.connected_toSimpleGraph
end SizeRamsey.Plan
