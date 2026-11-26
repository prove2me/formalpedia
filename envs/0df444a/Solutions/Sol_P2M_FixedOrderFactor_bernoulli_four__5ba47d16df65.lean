-- Prove2me | solution 1 for P2M_FixedOrderFactor_bernoulli_four__5ba47d16df65
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:19.174935+00:00
-- url     : https://prove2.me/submissions/7cc6ea71-3c17-41d7-867b-de55c71fd561

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
end FixedOrderFactor
