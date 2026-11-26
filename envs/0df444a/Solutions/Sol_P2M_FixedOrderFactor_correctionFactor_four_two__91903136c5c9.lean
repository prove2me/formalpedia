-- Prove2me | solution 1 for P2M_FixedOrderFactor_correctionFactor_four_two__91903136c5c9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:14.981342+00:00
-- url     : https://prove2.me/submissions/eef5f18d-40f0-4ff9-b825-ae7d0c3d4b98

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_correctionFactor_empty_four
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : correctionFactor {two} 4 = 35 / 34 := by
  rw [correctionFactor_eq_mul' _ (by norm_num), correctionFactor_empty_four,
    Finset.prod_singleton]
  simp [two]; norm_num
end FixedOrderFactor
