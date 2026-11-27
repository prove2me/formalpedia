-- Prove2me | solution 1 for SizeRamsey.Plan.three_le_degree_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:21:12.978015+00:00
-- url     : https://prove2.me/submissions/9fa6c224-8a64-4aa6-bbc9-5d428948dc2b

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
theorem _root_.solution {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ G.degree x := by
  have := degree_ge_card_of_subset G x {a, b, c} (by simp [ha, hb, hc])
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
end SizeRamsey.Plan
