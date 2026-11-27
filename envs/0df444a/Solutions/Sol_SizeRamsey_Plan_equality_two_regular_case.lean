-- Prove2me | solution 1 for SizeRamsey.Plan.equality_two_regular_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:26.540132+00:00
-- url     : https://prove2.me/submissions/a8df587a-455f-4359-9167-22d5ca9efb59

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Equality_TwoRegular
public import Theorems.Thm_SizeRamsey_Plan_equality_square_supported
public import Theorems.Thm_SizeRamsey_Plan_two_regular_square_supported


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (ht : Tight G)
    (h2 : ∀ v, G.degree v = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 4) := by
  exact two_regular_square_supported G hc (equality_square_supported G ht) h2
end SizeRamsey.Plan
