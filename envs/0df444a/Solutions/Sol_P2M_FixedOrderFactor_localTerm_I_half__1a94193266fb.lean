-- Prove2me | solution 1 for P2M_FixedOrderFactor_localTerm_I_half__1a94193266fb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:23.730266+00:00
-- url     : https://prove2.me/submissions/43494124-6c3b-4d83-badf-ad4d76d7f146

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 := by
  constructor <;> · simp [localTerm, Complex.normSq_apply]; norm_num
end FixedOrderFactor
