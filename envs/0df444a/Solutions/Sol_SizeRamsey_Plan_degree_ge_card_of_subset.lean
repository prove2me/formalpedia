-- Prove2me | solution 1 for SizeRamsey.Plan.degree_ge_card_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:37.240022+00:00
-- url     : https://prove2.me/submissions/b6a9e35c-cf06-4581-a4d2-558f92ea33c0

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution (x : V) (s : Finset V) (hs : ∀ y ∈ s, G.Adj x y) :
    s.card ≤ G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  exact Finset.card_le_card fun y hy => (G.mem_neighborFinset x y).mpr (hs y hy)
end SizeRamsey.Plan
