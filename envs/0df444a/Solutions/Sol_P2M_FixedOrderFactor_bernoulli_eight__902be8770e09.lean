-- Prove2me | solution 1 for P2M_FixedOrderFactor_bernoulli_eight__902be8770e09
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:26.242913+00:00
-- url     : https://prove2.me/submissions/5a037bb8-cc35-4dc0-a1ef-7aa861b9fcc6

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_b8

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), b8]
end FixedOrderFactor
