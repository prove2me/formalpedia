-- Prove2me | solution 1 for SizeRamsey.Plan.two_le_degree_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:06.457383+00:00
-- url     : https://prove2.me/submissions/48013a36-c9b7-481d-b0bb-d0c3c4a65931

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
public import Theorems.Thm_SizeRamsey_Plan_degree_ge_card_of_subset

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution {x a b : V} (ha : G.Adj x a) (hb : G.Adj x b) (hab : a ≠ b) :
    2 ≤ G.degree x := by
  have := degree_ge_card_of_subset G x {a, b} (by simp [ha, hb])
  rwa [Finset.card_pair hab] at this
end SizeRamsey.Plan
