-- Prove2me | solution 1 for SizeRamsey.Plan.rightCopy_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:23.303803+00:00
-- url     : https://prove2.me/submissions/468047eb-1add-49f2-bbc2-c044ac210ec6

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution (i j : Fin 6) :
    F17.Adj (rightCopy i) (rightCopy j) ↔
      k33MinusEdge.Adj i j := by
  fin_cases i <;> fin_cases j <;> decide
end SizeRamsey.Plan
