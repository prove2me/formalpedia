-- Prove2me | solution 1 for SizeRamsey.Plan.equality_min_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:26.045154+00:00
-- url     : https://prove2.me/submissions/118ca778-0486-4273-b247-c290e89be426

module
public import Definitions.Def_SizeRamsey_Universal
public import Definitions.Def_SizeRamsey_Tightness
public import Theorems.Thm_SizeRamsey_Plan_equality_square_supported
public import Theorems.Thm_SizeRamsey_Plan_connected_positive_degree
public import Theorems.Thm_SizeRamsey_Plan_square_supported_degree_ge_two


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
    (hcon : G.Connected) (hm : 0 < edgeCount G)
    (ht : 4 * tau4 G = edgeCount G) :
    ∀ v, 2 ≤ G.degree v := by
  intro v
  exact square_supported_degree_ge_two G (equality_square_supported G ht) v
    (connected_positive_degree G hcon hm v)
end SizeRamsey.Plan
