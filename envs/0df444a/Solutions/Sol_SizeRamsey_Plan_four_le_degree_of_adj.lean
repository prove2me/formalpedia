-- Prove2me | solution 1 for SizeRamsey.Plan.four_le_degree_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:06.868275+00:00
-- url     : https://prove2.me/submissions/4cdde1f5-e14a-472b-ab68-51392a875a79

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
theorem _root_.solution {x a b c d : V} (ha : G.Adj x a) (hb : G.Adj x b)
    (hc : G.Adj x c) (hd : G.Adj x d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ G.degree x := by
  have := degree_ge_card_of_subset G x {a, b, c, d} (by simp [ha, hb, hc, hd])
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd] at this
end SizeRamsey.Plan
